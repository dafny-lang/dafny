using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {

  /// <summary>
  /// Database that cancels pending document updates when new changes are incoming.
  /// </summary>
  /// <remarks>
  /// Only delta updates are supported and the API is not thread-safe.
  /// </remarks>
  public class DocumentDatabase : IDocumentDatabase {

    record DocumentState(DocumentObserver Observer, CompilationManager CompilationManager,
      IDisposable ObserverSubscription);

    private readonly IServiceProvider services;
    private readonly ILogger logger;
    private readonly ITelemetryPublisher telemetryPublisher;
    private readonly INotificationPublisher notificationPublisher;
    private readonly DocumentOptions options;
    private readonly Dictionary<DocumentUri, DocumentState> documents = new();
    private readonly ITextDocumentLoader documentLoader;
    private readonly ITextChangeProcessor textChangeProcessor;
    private readonly IRelocator relocator;

    private bool VerifyOnOpen => options.Verify == AutoVerification.OnChange;
    private bool VerifyOnChange => options.Verify == AutoVerification.OnChange;
    private bool VerifyOnSave => options.Verify == AutoVerification.OnSave;

    public DocumentDatabase(
      IServiceProvider services,
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

    public void OpenDocument(DocumentTextBuffer document) {
      var observer = new DocumentObserver(logger, telemetryPublisher, notificationPublisher, documentLoader, document);
      var compilationManager = new CompilationManager(services, document, VerifyOnOpen);
      var subscription = compilationManager.DocumentUpdates.Subscribe(observer);
      documents.Add(document.Uri, new DocumentState(observer, compilationManager, subscription));
    }

    public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
      var documentUri = documentChange.TextDocument.Uri;
      if (!documents.TryGetValue(documentUri, out var state)) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }

      var previousCompilationManager = state.CompilationManager;

      // According to the LSP specification, document versions should increase monotonically but may be non-consecutive.
      // See: https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/specification-3-16.md?plain=1#L1195
      var oldVer = previousCompilationManager.TextBuffer.Version;
      var newVer = documentChange.TextDocument.Version;
      if (oldVer >= newVer) {
        throw new InvalidOperationException(
          $"the updates of document {documentUri} are out-of-order: {oldVer} -> {newVer}");
      }

      previousCompilationManager.CancelPendingUpdates();
      var updatedText = textChangeProcessor.ApplyChange(previousCompilationManager.TextBuffer, documentChange, CancellationToken.None);

      var newCompilationManager = new CompilationManager(
        services,
        updatedText,
        VerifyOnChange
      );

      state.ObserverSubscription.Dispose();

      var newSubscription = newCompilationManager.DocumentUpdates.Select(d => {
        // TODO merge this document with the latest published document before the change, to implement migration.
        return d;
      }).Subscribe(state.Observer);

      documents[documentUri] = new DocumentState(state.Observer, newCompilationManager, newSubscription);
    }

    public void SaveDocument(TextDocumentIdentifier documentId) {
      if (!documents.TryGetValue(documentId.Uri, out var documentState)) {
        throw new ArgumentException($"the document {documentId.Uri} was not loaded before");
      }
      if (!VerifyOnSave) {
        return;
      }

      documentState.CompilationManager.Verify();
    }

    public async Task<bool> CloseDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.Remove(documentId.Uri, out var state)) {
        state.CompilationManager.CancelPendingUpdates();
        try {
          await state.CompilationManager.LastDocument;
        } catch (TaskCanceledException) {
        }
        return true;
      }
      return false;
    }
    private async Task<DafnyDocument> GetResolvedDocumentAsync(DocumentTextBuffer updatedText, CompilationManager compilationManager,
      DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {

      var oldDocument = compilationManager.LastPublishedDocument;

      // We do not pass the cancellation token to the text change processor because the text has to be kept in sync with the LSP client.
      var oldVerificationDiagnostics = oldDocument.ImplementationIdToView;
      var migratedImplementationViews = MigrateImplementationViews(documentChange, oldVerificationDiagnostics);
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
            ImplementationIdToView = new (migratedImplementationViews),
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
          ImplementationIdToView = new (migratedImplementationViews),
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
          VerificationTree = migratedVerificationTree,
          LoadCanceled = true,
          ImplementationIdToView = new (migratedImplementationViews),
          LastTouchedMethodPositions = migratedLastTouchedPositions
        };
      }
    }

    private Dictionary<ImplementationId, ImplementationView> MigrateImplementationViews(DidChangeTextDocumentParams documentChange,
      IReadOnlyDictionary<ImplementationId, ImplementationView> oldVerificationDiagnostics) {
      var result = new Dictionary<ImplementationId, ImplementationView>();
      foreach (var entry in oldVerificationDiagnostics) {
        var newRange = relocator.RelocateRange(entry.Value.Range, documentChange, CancellationToken.None);
        if (newRange != null) {
          result.Add(entry.Key with {
            NamedVerificationTask = relocator.RelocatePosition(entry.Key.NamedVerificationTask, documentChange, CancellationToken.None)
          }, entry.Value with {
            Range = newRange,
            Diagnostics = relocator.RelocateDiagnostics(entry.Value.Diagnostics, documentChange, CancellationToken.None)
          });
        }
      }
      return result;
    }

    private static bool RequiresOnSaveVerification(DafnyDocument document) {
      return document.LoadCanceled || document.SymbolTable.Resolved;
    }

    public Task<DafnyDocument?> GetResolvedDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        // TODO use migrated resolved state in case resolution failed.
        return databaseEntry.CompilationManager.ResolvedDocument!;
      }
      return Task.FromResult<DafnyDocument?>(null);
    }

    public Task<DafnyDocument?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return databaseEntry.CompilationManager.LastDocument!;
      }
      return Task.FromResult<DafnyDocument?>(null);
    }

    public IReadOnlyDictionary<DocumentUri, CompilationManager> Documents =>
      documents.ToDictionary(k => k.Key, v => v.Value.CompilationManager);

  }
}
