#nullable enable
using System;
using System.Collections.Generic;
using System.Reactive.Subjects;
using System.Threading;
using DafnyCore;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny {
  public class ObservableErrorReporter : ErrorReporter {
    private readonly Subject<NewDiagnostic> updates = new();
    public IObservable<NewDiagnostic> Updates => updates;

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

    protected override bool MessageCore(MessageSource source, ErrorLevel level, string? errorId, IOrigin rootTok, string msg) {
      if (ErrorsOnly && level != ErrorLevel.Error) {
        return false;
      }
      var relatedInformation = new List<DafnyRelatedInformation>();

      var usingSnippets = Options.Get(Snippets.ShowSnippets);
      if (rootTok is NestedOrigin nestedToken) {
        relatedInformation.AddRange(
          ErrorReporterExtensions.CreateDiagnosticRelatedInformationFor(
            nestedToken.Inner, nestedToken.Message, usingSnippets)
        );
      }

      var dafnyDiagnostic = new DafnyDiagnostic(source, errorId!, rootTok, msg, level, relatedInformation);
      AddDiagnosticForFile(dafnyDiagnostic, GetUriOrDefault(rootTok));
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

    private void AddDiagnosticForFile(DafnyDiagnostic dafnyDiagnostic, Uri uri) {
      rwLock.EnterWriteLock();
      try {
        counts[dafnyDiagnostic.Level] = counts.GetValueOrDefault(dafnyDiagnostic.Level, 0) + 1;
        if (dafnyDiagnostic.Source != MessageSource.Verifier && dafnyDiagnostic.Source != MessageSource.Compiler) {
          countsNotVerificationOrCompiler[dafnyDiagnostic.Level] =
            countsNotVerificationOrCompiler.GetValueOrDefault(dafnyDiagnostic.Level, 0) + 1;
        }
        updates.OnNext(new NewDiagnostic(uri, dafnyDiagnostic));
      }
      finally {
        rwLock.ExitWriteLock();
      }
    }

    private Uri GetUriOrDefault(IOrigin token) {
      return token.Filepath == null
        ? entryUri
        : token.Uri;
    }
  }
}
