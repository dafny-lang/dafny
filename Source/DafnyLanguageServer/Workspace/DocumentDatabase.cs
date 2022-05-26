using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Linq;
using System.Reactive.Threading.Tasks;
using System.Runtime.CompilerServices;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Workspace {

  /// <summary>
  /// Database that cancels pending document updates when new changes are incoming.
  /// </summary>
  /// <remarks>
  /// Only delta updates are supported and the API is not thread-safe.
  /// </remarks>
  public class DocumentDatabase : IDocumentDatabase {
    private readonly ILogger logger;
    private readonly DocumentOptions options;
    private readonly Dictionary<DocumentUri, DocumentEntry> documents = new();
    private readonly ITextDocumentLoader documentLoader;
    private readonly ITextChangeProcessor textChangeProcessor;
    private readonly IRelocator relocator;

    private bool VerifyOnOpen => options.Verify == AutoVerification.OnChange;
    private bool VerifyOnChange => options.Verify == AutoVerification.OnChange;
    private bool VerifyOnSave => options.Verify == AutoVerification.OnSave;

    public DocumentDatabase(
      ILogger<DocumentDatabase> logger,
      IOptions<DocumentOptions> options,
      ITextDocumentLoader documentLoader,
      ITextChangeProcessor textChangeProcessor,
      IRelocator relocator
    ) {
      this.logger = logger;
      this.options = options.Value;
      this.documentLoader = documentLoader;
      this.textChangeProcessor = textChangeProcessor;
      this.relocator = relocator;
      DafnyOptions.O.ProverOptions = GetProverOptions(this.options);
    }

    private static List<string> GetProverOptions(DocumentOptions options) {
      return options.ProverOptions.Split(
        new[] { " ", "\n", "\t" },
        StringSplitOptions.RemoveEmptyEntries
      ).ToList();
    }

    public async Task<bool> CloseDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.Remove(documentId.Uri, out var databaseEntry)) {
        databaseEntry.CancelPendingUpdates();
        try {
          await databaseEntry.LastDocument;
        } catch (TaskCanceledException) {
        }
        return true;
      }
      return false;
    }

    public IObservable<DafnyDocument> OpenDocument(DocumentTextBuffer document) {
      var cancellationSource = new CancellationTokenSource();
      var resolvedDocumentTask = OpenAsync(document, cancellationSource.Token);

      var translatedDocument = LoadVerificationTasksAsync(resolvedDocumentTask, cancellationSource.Token);
      var verifiedDocuments = Verify(translatedDocument, VerifyOnOpen, cancellationSource.Token);

      documents.Add(document.Uri, new DocumentEntry(
        document.Version,
        resolvedDocumentTask,
        translatedDocument,
        verifiedDocuments,
        cancellationSource
      ));
      return resolvedDocumentTask.ToObservable().Where(d => !d.LoadCanceled).
        Concat(translatedDocument.ToObservable()).
        Concat(verifiedDocuments);
    }

    private Task<DafnyDocument> LoadVerificationTasksAsync(Task<DafnyDocument> resolvedDocumentTask, CancellationToken cancellationToken) {

#pragma warning disable VSTHRD003
      return resolvedDocumentTask.SelectMany(resolvedDocument =>
        documentLoader.PrepareVerificationTasksAsync(resolvedDocument, cancellationToken));
#pragma warning restore VSTHRD003
    }

    private async Task<DafnyDocument> OpenAsync(DocumentTextBuffer textDocument, CancellationToken cancellationToken) {
      try {
        var newDocument = await documentLoader.LoadAsync(textDocument, cancellationToken);
        documentLoader.PublishGutterIcons(newDocument, false);
        return newDocument;
      } catch (OperationCanceledException) {
        // We do not allow canceling the load of the placeholder document. Otherwise, other components
        // start to have to check for nullability in later stages such as change request processors.
        return documentLoader.CreateUnloaded(textDocument, CancellationToken.None);
      }
    }

    private IObservable<DafnyDocument> Verify(Task<DafnyDocument> withVerificationTasks, bool verify, CancellationToken cancellationToken) {
      if (!verify) {
        return Observable.Empty<DafnyDocument>();
      }

      return withVerificationTasks.ContinueWith(task => {
        if (task.IsCanceled) {
          return Observable.Empty<DafnyDocument>();
        }

        var document = task.Result;
        if (!RequiresOnSaveVerification(document)) {
          return Observable.Empty<DafnyDocument>();
        }

        return documentLoader.Verify(document, cancellationToken);
      }, TaskScheduler.Current).ToObservable().Merge();
    }

    public IObservable<DafnyDocument> UpdateDocument(DidChangeTextDocumentParams documentChange) {
      var documentUri = documentChange.TextDocument.Uri;
      if (!documents.TryGetValue(documentUri, out var databaseEntry)) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }

      // According to the LSP specification, document versions should increase monotonically but may be non-consecutive.
      // See: https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/specification-3-16.md?plain=1#L1195
      var oldVer = databaseEntry.Version;
      var newVer = documentChange.TextDocument.Version;
      if (oldVer >= newVer) {
        throw new InvalidOperationException(
          $"the updates of document {documentUri} are out-of-order: {oldVer} -> {newVer}");
      }

      databaseEntry.CancelPendingUpdates();
      var cancellationSource = new CancellationTokenSource();
      var previousDocumentTask = databaseEntry.LatestDocument;
      var resolvedDocumentTask = ApplyChangesAsync(previousDocumentTask, documentChange, cancellationSource.Token);
      var translatedDocument =
        LoadVerificationTasksAsync(previousDocumentTask, resolvedDocumentTask, cancellationSource.Token);
      var verifiedDocuments = Verify(translatedDocument, VerifyOnChange, cancellationSource.Token);
      documents[documentUri] = new DocumentEntry(
        documentChange.TextDocument.Version,
        resolvedDocumentTask,
        translatedDocument,
        verifiedDocuments,
        cancellationSource
      );
      return resolvedDocumentTask.ToObservable().
        Concat(translatedDocument.ToObservable()).
        Concat(verifiedDocuments);
    }

    private async Task<DafnyDocument> ApplyChangesAsync(Task<DafnyDocument> oldDocumentTask, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
#pragma warning disable VSTHRD003
      var oldDocument = await oldDocumentTask;
#pragma warning restore VSTHRD003

      // We do not pass the cancellation token to the text change processor because the text has to be kept in sync with the LSP client.
      var updatedText = textChangeProcessor.ApplyChange(oldDocument.TextDocumentItem, documentChange, CancellationToken.None);
      var oldVerificationDiagnostics = oldDocument.ImplementationViews ?? new Dictionary<ImplementationId, ImplementationView>();
      var migratedImplementationViews = oldVerificationDiagnostics.ToDictionary(
        kv => kv.Key with {
          NamedVerificationTask =
          relocator.RelocatePosition(kv.Key.NamedVerificationTask, documentChange, CancellationToken.None)
        },
        kv => kv.Value with {
          Diagnostics = relocator.RelocateDiagnostics(kv.Value.Diagnostics, documentChange, CancellationToken.None)
        });
      var migratedVerificationTree =
        relocator.RelocateVerificationTree(oldDocument.VerificationTree, updatedText.NumberOfLines, documentChange, CancellationToken.None);

      var migratedLastTouchedPositions =
        relocator.RelocatePositions(oldDocument.LastTouchedMethodPositions, documentChange, CancellationToken.None);
      try {
        var newDocument = await documentLoader.LoadAsync(updatedText, cancellationToken);
        var lastChange =
          documentChange.ContentChanges
            .Select(contentChange => contentChange.Range)
            .LastOrDefault(newDocument.LastChange);
        newDocument = newDocument with { LastChange = lastChange };
        if (newDocument.SymbolTable.Resolved) {
          var resolvedDocument = newDocument with {
            ImplementationViews = migratedImplementationViews,
            VerificationTree = migratedVerificationTree,
            LastTouchedMethodPositions = migratedLastTouchedPositions
          };
          documentLoader.PublishGutterIcons(resolvedDocument, false);
          return resolvedDocument;
        }
        // The document loader failed to create a new symbol table. Since we'd still like to provide
        // features such as code completion and lookup, we re-locate the previously resolved symbols
        // according to the change.
        var failedDocument = newDocument with {
          SymbolTable = relocator.RelocateSymbols(oldDocument.SymbolTable, documentChange, CancellationToken.None),
          ImplementationViews = migratedImplementationViews,
          VerificationTree = migratedVerificationTree,
          LastTouchedMethodPositions = migratedLastTouchedPositions
        };
        documentLoader.PublishGutterIcons(failedDocument, false);
        return failedDocument;
      } catch (OperationCanceledException) {
        // The document load was canceled before it could complete. We migrate the document
        // to re-locate symbols that were resolved previously.
        logger.LogTrace("document loading canceled, applying migration");
        return oldDocument with {
          TextDocumentItem = updatedText,
          SymbolTable = relocator.RelocateSymbols(oldDocument.SymbolTable, documentChange, CancellationToken.None),
          CounterExamples = Array.Empty<Counterexample>(),
          VerificationTree = migratedVerificationTree,
          LoadCanceled = true,
          ImplementationViews = migratedImplementationViews,
          LastTouchedMethodPositions = migratedLastTouchedPositions
        };
      }
    }

    private async Task<DafnyDocument> LoadVerificationTasksAsync(Task<DafnyDocument> oldDocumentTask,
      Task<DafnyDocument> resolvedDocumentTask, CancellationToken cancellationToken) {
#pragma warning disable VSTHRD003
      var oldDocument = await oldDocumentTask;
      var resolvedDocument = await resolvedDocumentTask;
#pragma warning restore VSTHRD003
      var withVerificationTasks = await documentLoader.PrepareVerificationTasksAsync(resolvedDocument, cancellationToken);
      var oldViews = oldDocument.ImplementationViews ?? new Dictionary<ImplementationId, ImplementationView>();
      return withVerificationTasks with {
        ImplementationViews = withVerificationTasks.ImplementationViews!.ToDictionary(
          kv => kv.Key,
          kv =>
            kv.Value with {
              Diagnostics = oldViews.GetValueOrDefault(kv.Key)?.Diagnostics ?? kv.Value.Diagnostics
            }
        ),
      };
    }

    public IObservable<DafnyDocument> SaveDocument(TextDocumentIdentifier documentId) {
      if (!documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        throw new ArgumentException($"the document {documentId.Uri} was not loaded before");
      }
      if (!VerifyOnSave) {
        return Observable.Empty<DafnyDocument>();
      }

      var cancellationSource = new CancellationTokenSource();
      var verifiedDocuments = Verify(databaseEntry.TranslatedDocument, true, cancellationSource.Token);
      documents[documentId.Uri] = new DocumentEntry(
        databaseEntry.Version,
        databaseEntry.ResolvedDocument,
        databaseEntry.TranslatedDocument,
        verifiedDocuments,
        cancellationSource
      );
      return verifiedDocuments;
    }

    private static bool RequiresOnSaveVerification(DafnyDocument document) {
      return document.LoadCanceled || document.SymbolTable.Resolved;
    }

    public Task<DafnyDocument?> GetDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return databaseEntry.ResolvedDocument!;
      }
      return Task.FromResult<DafnyDocument?>(null);
    }

    public Task<DafnyDocument?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return databaseEntry.LastDocument!;
      }
      return Task.FromResult<DafnyDocument?>(null);
    }

    public IReadOnlyDictionary<DocumentUri, IDocumentEntry> Documents =>
      documents.ToDictionary(k => k.Key, v => (IDocumentEntry)v.Value);

    private class DocumentEntry : IDocumentEntry {
      private readonly CancellationTokenSource cancellationSource;
      public int? Version { get; }
      public Task<DafnyDocument> ResolvedDocument { get; }
      public Task<DafnyDocument> TranslatedDocument { get; }

      public DocumentEntry(int? version,
        Task<DafnyDocument> resolvedDocument,
        Task<DafnyDocument> translatedDocument,
        IObservable<DafnyDocument> verifiedDocuments,
        CancellationTokenSource cancellationSource) {
        this.cancellationSource = cancellationSource;
        TranslatedDocument = translatedDocument;
        Version = version;
        ResolvedDocument = resolvedDocument;
        LatestDocument = resolvedDocument;
        TranslatedDocument.ToObservable().Concat(verifiedDocuments).
          Subscribe(update => LatestDocument = Task.FromResult(update), e => { });
        LastDocument = ResolvedDocument.ToObservable().Concat(verifiedDocuments).ToTask();
      }

      public void CancelPendingUpdates() {
        cancellationSource.Cancel();
      }

      public Task<DafnyDocument> LatestDocument { get; private set; }

      public Task<DafnyDocument> LastDocument { get; }
    }
  }
}
