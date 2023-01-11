using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Util;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using VCGeneration;
using Newtonsoft.Json.Linq;

namespace Microsoft.Dafny.LanguageServer.Language {
  public class DiagnosticErrorReporter : ErrorReporter {
    private const MessageSource VerifierMessageSource = MessageSource.Verifier;
    private const string RelatedLocationCategory = "Related location";
    private const string RelatedLocationMessage = RelatedLocationCategory;

    private readonly DocumentUri entryDocumentUri;
    private readonly Dictionary<DocumentUri, List<Diagnostic>> diagnostics = new();
    private readonly Dictionary<DiagnosticSeverity, int> counts = new();
    private readonly Dictionary<DiagnosticSeverity, int> countsNotVerificationOrCompiler = new();
    private readonly ReaderWriterLockSlim rwLock = new();

    /// <summary>
    /// Creates a new instance with the given uri of the entry document.
    /// </summary>
    /// <param name="entryDocumentUri">The entry document's uri.</param>
    /// <remarks>
    /// The uri of the entry document is necessary to report general compiler errors as part of this document.
    /// </remarks>
    public DiagnosticErrorReporter(string documentSource, DocumentUri entryDocumentUri) {
      this.entryDocumentsource = documentSource;
      this.entryDocumentUri = entryDocumentUri;
    }

    public IReadOnlyDictionary<DocumentUri, List<Diagnostic>> AllDiagnostics => diagnostics;

    public IReadOnlyList<Diagnostic> GetDiagnostics(DocumentUri documentUri) {
      rwLock.EnterReadLock();
      try {
        // Concurrency: Return a copy of the list not to expose a reference to an object that requires synchronization.
        // LATER: Make the Diagnostic type immutable, since we're not protecting it from concurrent accesses
        return new List<Diagnostic>(
          diagnostics.GetValueOrDefault(documentUri) ??
          Enumerable.Empty<Diagnostic>());
      }
      finally {
        rwLock.ExitReadLock();
      }
    }

    public void ReportBoogieError(ErrorInformation error) {
      var relatedInformation = new List<DiagnosticRelatedInformation>();
      foreach (var auxiliaryInformation in error.Aux) {
        if (auxiliaryInformation.Category == RelatedLocationCategory) {
          relatedInformation.AddRange(CreateDiagnosticRelatedInformationFor(Translator.ToDafnyToken(auxiliaryInformation.Tok), auxiliaryInformation.Msg));
        } else {
          // The execution trace is an additional auxiliary which identifies itself with
          // line=0 and character=0. These positions cause errors when exposing them, Furthermore,
          // the execution trace message appears to not have any interesting information.
          if (auxiliaryInformation.Tok.line > 0) {
            Info(VerifierMessageSource, Translator.ToDafnyToken(auxiliaryInformation.Tok), auxiliaryInformation.Msg);
          }
        }
      }

      if (error.Tok is NestedToken { Inner: var innerToken }) {
        relatedInformation.AddRange(CreateDiagnosticRelatedInformationFor(innerToken, "Related location"));
      }

      var uri = GetDocumentUriOrDefault(Translator.ToDafnyToken(error.Tok));
      var diagnostic = new Diagnostic {
        Severity = DiagnosticSeverity.Error,
        Message = error.Msg,
        Range = error.Tok.GetLspRange(),
        RelatedInformation = relatedInformation,
        Source = VerifierMessageSource.ToString()
      };
      AddDiagnosticForFile(
        diagnostic,
        VerifierMessageSource,
        uri
      );
    }

    public static readonly string PostConditionFailingMessage = new EnsuresDescription().FailureDescription;
    private readonly string entryDocumentsource;

    public static string FormatRelated(string related) {
      return $"Could not prove: {related}";
    }

    private IEnumerable<DiagnosticRelatedInformation> CreateDiagnosticRelatedInformationFor(IToken token, string message) {
      var (tokenForMessage, inner) = token is NestedToken nestedToken ? (nestedToken.Outer, nestedToken.Inner) : (token, null);
      if (tokenForMessage is RangeToken range) {
        var rangeLength = range.EndToken.pos + range.EndToken.val.Length - range.StartToken.pos;
        if (message == PostConditionFailingMessage) {
          var postcondition = entryDocumentsource.Substring(range.StartToken.pos, rangeLength);
          message = $"This postcondition might not hold: {postcondition}";
        } else if (message == "Related location") {
          var tokenUri = tokenForMessage.GetDocumentUri();
          if (tokenUri == entryDocumentUri) {
            message = FormatRelated(entryDocumentsource.Substring(range.StartToken.pos, rangeLength));
          } else {
            var fileName = tokenForMessage.GetDocumentUri().GetFileSystemPath();
            message = "";
            try {
              var content = File.ReadAllText(fileName);
              message = FormatRelated(content.Substring(range.StartToken.pos, rangeLength));
            } catch (IOException) {
              message = message + "(could not open file " + fileName + ")";
            } catch (ArgumentOutOfRangeException) {
              message = "Related location (could not read position in file " + fileName + ")";
            }
            if (message == "") {
              message = "Related location (could not read file " + fileName + ")";
            }
          }
        }
      }

      yield return new DiagnosticRelatedInformation {
        Message = message,
        Location = CreateLocation(token)
      };
      if (inner != null) {
        foreach (var nestedInformation in CreateDiagnosticRelatedInformationFor(inner, RelatedLocationMessage)) {
          yield return nestedInformation;
        }
      }
    }

    private static Location CreateLocation(IToken token) {
      var uri = DocumentUri.Parse(token.filename);
      return new Location {
        Range = token.GetLspRange(),
        // During parsing, we store absolute paths to make reconstructing the Uri easier
        // https://github.com/dafny-lang/dafny/blob/06b498ee73c74660c61042bb752207df13930376/Source/DafnyLanguageServer/Language/DafnyLangParser.cs#L59 
        Uri = uri
      };
    }

    public override bool Message(MessageSource source, ErrorLevel level, string errorID, IToken tok, string msg) {
      if (ErrorsOnly && level != ErrorLevel.Error) {
        return false;
      }
      var relatedInformation = new List<DiagnosticRelatedInformation>();
      var ntok = tok;
      while (ntok is NestedToken nestedToken) {
        ntok = nestedToken.Inner;
        if (!(ntok is CodeActionToken)) {
          relatedInformation.AddRange(
            CreateDiagnosticRelatedInformationFor(
              ntok, nestedToken.Message ?? "Related location")
          );
          break;
        }
      }

      var item = new Diagnostic {
        Code = errorID,
        Severity = ToSeverity(level),
        Message = msg,
        Range = tok.GetLspRange(),
        Source = source.ToString(),
        RelatedInformation = relatedInformation,
        CodeDescription = errorID == "" ? null : new CodeDescription { Href = new System.Uri("https://dafny.org/dafny/docs/HowToFAQ/Errors#" + errorID) },
        Data = JToken.FromObject(Errors.FindCodeActionRange(tok).GetLspRange()),
      };
      AddDiagnosticForFile(item, source, GetDocumentUriOrDefault(tok));
      return true;
    }

    public override int Count(ErrorLevel level) {
      rwLock.EnterReadLock();
      try {
        return counts.GetValueOrDefault(ToSeverity(level), 0);
      }
      finally {
        rwLock.ExitReadLock();
      }
    }

    public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
      rwLock.EnterReadLock();
      try {
        return countsNotVerificationOrCompiler.GetValueOrDefault(ToSeverity(level), 0);
      }
      finally {
        rwLock.ExitReadLock();
      }
    }

    private void AddDiagnosticForFile(Diagnostic item, MessageSource messageSource, DocumentUri documentUri) {
      rwLock.EnterWriteLock();
      try {
        var severity = item.Severity!.Value; // All our diagnostics have a severity.
        counts[severity] = counts.GetValueOrDefault(severity, 0) + 1;
        if (messageSource != MessageSource.Verifier && messageSource != MessageSource.Compiler) {
          countsNotVerificationOrCompiler[severity] =
            countsNotVerificationOrCompiler.GetValueOrDefault(severity, 0) + 1;
        }
        diagnostics.GetOrCreate(documentUri, () => new List<Diagnostic>()).Add(item);
      }
      finally {
        rwLock.ExitWriteLock();
      }
    }

    private DocumentUri GetDocumentUriOrDefault(IToken token) {
      return token.Filename == null
        ? entryDocumentUri
        : token.GetDocumentUri();
    }

    private static DiagnosticSeverity ToSeverity(ErrorLevel level) {
      return level switch {
        ErrorLevel.Error => DiagnosticSeverity.Error,
        ErrorLevel.Warning => DiagnosticSeverity.Warning,
        ErrorLevel.Info => DiagnosticSeverity.Hint,
        _ => throw new ArgumentException($"unknown error level {level}", nameof(level))
      };
    }
  }
}
