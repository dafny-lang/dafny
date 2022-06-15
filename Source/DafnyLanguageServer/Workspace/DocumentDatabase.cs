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
    private readonly ITelemetryPublisher telemetryPublisher;
    private readonly INotificationPublisher notificationPublisher;
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
      ITelemetryPublisher telemetryPublisher,
      INotificationPublisher notificationPublisher,
      IOptions<DocumentOptions> options,
      ITextDocumentLoader documentLoader,
      ITextChangeProcessor textChangeProcessor,
      IRelocator relocator
    ) {
      this.logger = logger;
      this.telemetryPublisher = telemetryPublisher;
      this.notificationPublisher = notificationPublisher;
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
        databaseEntry.Observer.Dispose();
        databaseEntry.CancelPendingUpdates();
        try {
          await databaseEntry.LastDocument;
        } catch (TaskCanceledException) {
        }
        return true;
      }
      return false;
    }

    public void OpenDocument(DocumentTextBuffer document) {
      var cancellationSource = new CancellationTokenSource();
      var resolvedDocumentTask = OpenAsync(document, cancellationSource.Token);

      var translatedDocument = LoadVerificationTasksAsync(resolvedDocumentTask, cancellationSource.Token);

      var documentEntry = new DocumentEntry(
        document.Version,
        document,
        resolvedDocumentTask,
        translatedDocument,
        cancellationSource,
        new RequestUpdatesOnUriObserver(logger, telemetryPublisher, notificationPublisher, document)
      );
      documents.Add(document.Uri, documentEntry);

      documentEntry.Observe(
        resolvedDocumentTask.ToObservableSkipCancelled().Where(d => !d.LoadCanceled).
        Concat(translatedDocument.ToObservableSkipCancelled()));

      if (VerifyOnOpen) {
        Verify(documentEntry, cancellationSource.Token);
      }
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

    private void Verify(IDocumentEntry documentEntry, CancellationToken cancellationToken) {
      var withVerificationTasks = documentEntry.TranslatedDocument;

      var updates = withVerificationTasks.ContinueWith(task => {
        if (task.IsCanceled) {
          return Observable.Empty<DafnyDocument>();
        }

        var document = task.Result;
        if (!RequiresOnSaveVerification(document) || !document.CanDoVerification) {
          return Observable.Empty<DafnyDocument>();
        }

        return documentLoader.VerifyAllTasks(document, cancellationToken);
      }, TaskScheduler.Current).ToObservableSkipCancelled().Merge();
      documentEntry.Observe(updates);
    }

    public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
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
      var updatedText = textChangeProcessor.ApplyChange(databaseEntry.TextBuffer, documentChange, CancellationToken.None);
      var resolvedDocumentTask = ApplyChangesAsync(updatedText, databaseEntry, documentChange, cancellationSource.Token);
      var translatedDocument = LoadVerificationTasksAsync(resolvedDocumentTask, cancellationSource.Token);
      var entry = new DocumentEntry(
        documentChange.TextDocument.Version,
        updatedText,
        resolvedDocumentTask,
        translatedDocument,
        cancellationSource,
        databaseEntry.Observer
      );
      documents[documentUri] = entry;
      entry.Observe(resolvedDocumentTask.ToObservableSkipCancelled()
        .Concat(translatedDocument.ToObservableSkipCancelled()));

      if (VerifyOnChange) {
        Verify(entry, cancellationSource.Token);
      }
    }

    private async Task<DafnyDocument> ApplyChangesAsync(DocumentTextBuffer updatedText, DocumentEntry documentEntry, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {

      var oldDocument = documentEntry.LastPublishedDocument;

      // We do not pass the cancellation token to the text change processor because the text has to be kept in sync with the LSP client.
      var oldVerificationDiagnostics = oldDocument.ImplementationIdToView ?? new Dictionary<ImplementationId, ImplementationView>();
      var migratedImplementationViews = oldVerificationDiagnostics.ToDictionary(
        kv => kv.Key with {
          NamedVerificationTask =
          relocator.RelocatePosition(kv.Key.NamedVerificationTask, documentChange, CancellationToken.None)
        },
        kv => kv.Value with {
          Range = relocator.RelocateRange(kv.Value.Range, documentChange, CancellationToken.None),
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
            ImplementationIdToView = migratedImplementationViews,
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
          ImplementationIdToView = migratedImplementationViews,
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
          Counterexamples = Array.Empty<Counterexample>(),
          VerificationTree = migratedVerificationTree,
          LoadCanceled = true,
          ImplementationIdToView = migratedImplementationViews,
          LastTouchedMethodPositions = migratedLastTouchedPositions
        };
      }
    }

    private async Task<DafnyDocument> LoadVerificationTasksAsync(Task<DafnyDocument> resolvedDocumentTask, CancellationToken cancellationToken) {
#pragma warning disable VSTHRD003
      var resolvedDocument = await resolvedDocumentTask;
#pragma warning restore VSTHRD003
      var withVerificationTasks = await documentLoader.PrepareVerificationTasksAsync(resolvedDocument, cancellationToken);

      return withVerificationTasks with {
        ImplementationIdToView = withVerificationTasks.ImplementationIdToView.ToDictionary(
          kv => kv.Key,
          kv =>
            kv.Value with {
              Diagnostics = resolvedDocument.ImplementationIdToView.GetValueOrDefault(kv.Key)?.Diagnostics ?? kv.Value.Diagnostics
            }
        ),
      };
    }

    public void SaveDocument(TextDocumentIdentifier documentId) {
      if (!documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        throw new ArgumentException($"the document {documentId.Uri} was not loaded before");
      }
      if (!VerifyOnSave) {
        return;
      }

      var cancellationSource = new CancellationTokenSource();
      Verify(databaseEntry, cancellationSource.Token);
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
      public DocumentTextBuffer TextBuffer { get; }
      public Task<DafnyDocument> ResolvedDocument { get; }
      public Task<DafnyDocument> TranslatedDocument { get; }
      public DafnyDocument LastPublishedDocument => Observer.PreviouslyPublishedDocument;
      public Task<DafnyDocument> LastDocument => Observer.IdleChangesIncludingLast.Where(idle => idle).
        Select(_ => Observer.PreviouslyPublishedDocument).
        FirstAsync().ToTask();

      public DocumentEntry(int? version,
        DocumentTextBuffer textBuffer,
        Task<DafnyDocument> resolvedDocument,
        Task<DafnyDocument> translatedDocument,
        CancellationTokenSource cancellationSource,
        RequestUpdatesOnUriObserver observer) {
        this.cancellationSource = cancellationSource;
        Observer = observer;
        TranslatedDocument = translatedDocument;
        Version = version;
        TextBuffer = textBuffer;
        ResolvedDocument = resolvedDocument;
      }

      public void CancelPendingUpdates() {
        cancellationSource.Cancel();
      }

      public RequestUpdatesOnUriObserver Observer { get; }

      public void Observe(IObservable<DafnyDocument> updates) {
        Observer.OnNext(updates);
      }
    }
  }
}
