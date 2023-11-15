using System;
using System.Collections.Generic;
using System.Reactive.Subjects;
using System.Threading;
using Microsoft.Dafny.LanguageServer.Workspace;
using VCGeneration;

namespace Microsoft.Dafny.LanguageServer.Language {
  public class ObservableErrorReporter : ErrorReporter {
    private readonly Subject<NewDiagnostic> updates = new();
    public IObservable<NewDiagnostic> Updates => updates;

    private const MessageSource VerifierMessageSource = MessageSource.Verifier;
    private const string RelatedLocationCategory = "Related location";
    private const string RelatedLocationMessage = RelatedLocationCategory;

    private readonly Uri entryUri;
    private readonly Dictionary<ErrorLevel, int> counts = new();
    private readonly Dictionary<ErrorLevel, int> countsNotVerificationOrCompiler = new();
    private readonly ReaderWriterLockSlim rwLock = new();

    /// <summary>
    /// Creates a new instance with the given uri of the entry document.
    /// </summary>
    /// <param name="entryUri">The entry document's uri.</param>
    /// <remarks>
    /// The uri of the entry document is necessary to report general compiler errors as part of this document.
    /// </remarks>
    public ObservableErrorReporter(DafnyOptions options, Uri entryUri) : base(options) {
      this.entryUri = entryUri;
    }

    public void ReportBoogieError(ErrorInformation error, bool useRange = true) {
      var relatedInformation = new List<DafnyRelatedInformation>();
      foreach (var auxiliaryInformation in error.Aux) {
        if (auxiliaryInformation.Category == RelatedLocationCategory) {
          relatedInformation.AddRange(CreateDiagnosticRelatedInformationFor(BoogieGenerator.ToDafnyToken(true, auxiliaryInformation.Tok), auxiliaryInformation.Msg));
        } else {
          // The execution trace is an additional auxiliary which identifies itself with
          // line=0 and character=0. These positions cause errors when exposing them, Furthermore,
          // the execution trace message appears to not have any interesting information.
          if (auxiliaryInformation.Tok.line > 0) {
            Info(VerifierMessageSource, BoogieGenerator.ToDafnyToken(true, auxiliaryInformation.Tok), auxiliaryInformation.Msg);
          }
        }
      }

      if (error.Tok is NestedToken { Inner: var innerToken }) {
        relatedInformation.AddRange(CreateDiagnosticRelatedInformationFor(innerToken, "Related location"));
      }

      var dafnyToken = BoogieGenerator.ToDafnyToken(useRange, error.Tok);
      var uri = GetUriOrDefault(dafnyToken);
      var dafnyDiagnostic = new DafnyDiagnostic(null, dafnyToken, error.Msg,
        VerifierMessageSource, ErrorLevel.Error, relatedInformation);
      AddDiagnosticForFile(
        dafnyDiagnostic,
        VerifierMessageSource,
        uri
      );
    }

    public static readonly string PostConditionFailingMessage = new ProofObligationDescription.EnsuresDescription(null, null).FailureDescription;

    private static string FormatRelated(string related) {
      return $"Could not prove: {related}";
    }

    private IEnumerable<DafnyRelatedInformation> CreateDiagnosticRelatedInformationFor(IToken token, string message) {
      var (tokenForMessage, inner) = token is NestedToken nestedToken ? (nestedToken.Outer, nestedToken.Inner) : (token, null);
      var dafnyToken = BoogieGenerator.ToDafnyToken(true, tokenForMessage);
      if (dafnyToken is RangeToken rangeToken) {
        if (message == PostConditionFailingMessage) {
          var postcondition = rangeToken.PrintOriginal();
          message = $"This postcondition might not hold: {postcondition}";
        } else if (message == "Related location") {
          message = FormatRelated(rangeToken.PrintOriginal());
        }
      }

      yield return new DafnyRelatedInformation(token, message);
      if (inner != null) {
        foreach (var nestedInformation in CreateDiagnosticRelatedInformationFor(inner, RelatedLocationMessage)) {
          yield return nestedInformation;
        }
      }
    }

    protected override bool MessageCore(MessageSource source, ErrorLevel level, string? errorId, IToken rootTok, string msg) {
      if (ErrorsOnly && level != ErrorLevel.Error) {
        return false;
      }
      var relatedInformation = new List<DafnyRelatedInformation>();
      var tok = rootTok;
      while (tok is NestedToken nestedToken) {
        tok = nestedToken.Inner;
        if (!(tok is RangeToken)) {
          relatedInformation.AddRange(
            CreateDiagnosticRelatedInformationFor(
              tok, nestedToken.Message ?? "Related location")
          );
          break;
        }
      }

      var dafnyDiagnostic = new DafnyDiagnostic(errorId, rootTok, msg, source, level, relatedInformation);
      AddDiagnosticForFile(dafnyDiagnostic, source, GetUriOrDefault(rootTok));
      return true;
    }

    public override int Count(ErrorLevel level) {
      rwLock.EnterReadLock();
      try {
        return counts.GetValueOrDefault(level, 0);
      }
      finally {
        rwLock.ExitReadLock();
      }
    }

    public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
      rwLock.EnterReadLock();
      try {
        return countsNotVerificationOrCompiler.GetValueOrDefault(level, 0);
      }
      finally {
        rwLock.ExitReadLock();
      }
    }

    private void AddDiagnosticForFile(DafnyDiagnostic dafnyDiagnostic, MessageSource messageSource, Uri uri) {
      rwLock.EnterWriteLock();
      try {
        counts[dafnyDiagnostic.Level] = counts.GetValueOrDefault(dafnyDiagnostic.Level, 0) + 1;
        if (messageSource != MessageSource.Verifier && messageSource != MessageSource.Compiler) {
          countsNotVerificationOrCompiler[dafnyDiagnostic.Level] =
            countsNotVerificationOrCompiler.GetValueOrDefault(dafnyDiagnostic.Level, 0) + 1;
        }
        updates.OnNext(new NewDiagnostic(uri, dafnyDiagnostic));
      }
      finally {
        rwLock.ExitWriteLock();
      }
    }

    private Uri GetUriOrDefault(IToken token) {
      return token.Filepath == null
        ? entryUri
        : token.Uri;
    }
  }
}
