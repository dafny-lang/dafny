using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.DependencyInjection;

namespace Microsoft.Dafny.LanguageServer.Workspace {

  /// <summary>
  /// Database that cancels pending document updates when new changes are incoming.
  /// </summary>
  /// <remarks>
  /// Only delta updates are supported and the API is not thread-safe.
  /// </remarks>
  public class DocumentDatabase : IDocumentDatabase {

    record DocumentState(DocumentObserver Observer,
      CompilationManager CompilationManager,
      IDisposable ObserverSubscription);

    private readonly IServiceProvider services;
    private VerifierOptions VerifierOptions { get; }
    private readonly ILogger logger;
    private readonly ITelemetryPublisher telemetryPublisher;
    private readonly INotificationPublisher notificationPublisher;
    private readonly DocumentOptions documentOptions;
    private readonly Dictionary<DocumentUri, DocumentState> documents = new();
    private readonly ITextDocumentLoader documentLoader;
    private readonly ITextChangeProcessor textChangeProcessor;
    private readonly IRelocator relocator;

    private bool VerifyOnOpen => documentOptions.Verify == AutoVerification.OnChange;
    private bool VerifyOnChange => documentOptions.Verify == AutoVerification.OnChange;
    private bool VerifyOnSave => documentOptions.Verify == AutoVerification.OnSave;

    public DocumentDatabase(
      IServiceProvider services,
      DocumentOptions documentOptions,
      VerifierOptions verifierOptions) {
      this.services = services;
      logger = services.GetRequiredService<ILogger<DocumentDatabase>>();
      telemetryPublisher = services.GetRequiredService<ITelemetryPublisher>();
      notificationPublisher = services.GetRequiredService<INotificationPublisher>();
      documentLoader = services.GetRequiredService<ITextDocumentLoader>();
      textChangeProcessor = services.GetRequiredService<ITextChangeProcessor>();
      relocator = services.GetRequiredService<IRelocator>();
      this.documentOptions = documentOptions;
      VerifierOptions = verifierOptions;
      DafnyOptions.O.ProverOptions = GetProverOptions(this.documentOptions);
    }

    private static List<string> GetProverOptions(DocumentOptions options) {
      return options.ProverOptions.Split(
        new[] { " ", "\n", "\t" },
        StringSplitOptions.RemoveEmptyEntries
      ).ToList();
    }

    public void OpenDocument(DocumentTextBuffer document) {
      var observer = new DocumentObserver(logger, telemetryPublisher, notificationPublisher, documentLoader, document);
      var compilationManager = new CompilationManager(services, VerifierOptions, document, ImmutableList.Create<Position>(), VerifyOnOpen);
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

      var lastPublishedDocument = state.Observer.LastPublishedDocument;
      var oldVerificationDiagnostics = lastPublishedDocument.ImplementationIdToView;
      var migratedImplementationViews =
        oldVerificationDiagnostics == null ? null : MigrateImplementationViews(documentChange, oldVerificationDiagnostics);

      // TODO it would be simpler to store last touched positions at the DocumentState level, and always recompute the lastTouchedVerifiables from that.
      // Then we don't need to touch lastPublishedDocument.LastTouchedVerifiables which seems unreliable.
      var migratedLastTouchedVerifiables =
        relocator.RelocatePositions(lastPublishedDocument.LastTouchedVerifiables, documentChange, CancellationToken.None);

      // TODO use this.
      var migratedVerificationTree =
        relocator.RelocateVerificationTree(lastPublishedDocument.VerificationTree, updatedText.NumberOfLines, documentChange, CancellationToken.None);

      // TODO use this,
      // documentLoader.PublishGutterIcons(resolvedDocument, false);
      // Came from GetResolvedDocumentAsync

      var newCompilationManager = new CompilationManager(
        services,
        VerifierOptions,
        updatedText,
        migratedLastTouchedVerifiables,
        VerifyOnChange
      );

      state.ObserverSubscription.Dispose();
      var newSubscription = newCompilationManager.DocumentUpdates.Select(document => {
        if (!document.SymbolTable.Resolved) {
          document.SymbolTable = relocator.RelocateSymbols(lastPublishedDocument.SymbolTable, documentChange, CancellationToken.None);
        }

        var migratedViews = document.ImplementationIdToView?.Select(kv => {
          var value = kv.Value.Status < PublishedVerificationStatus.Error
            ? kv.Value with {
              Diagnostics = migratedImplementationViews != null && migratedImplementationViews.TryGetValue(kv.Key, out var previousView)
                ? previousView.Diagnostics
                : kv.Value.Diagnostics
            }
            : kv.Value;
          return new KeyValuePair<ImplementationId, ImplementationView>(kv.Key, value);
        }) ?? migratedImplementationViews;
        document.ImplementationIdToView = migratedViews == null ? null : new(migratedViews);

        return document;
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

    public async Task<DafnyDocument?> GetBestResolvedDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var state)) {
        try {
          await state.CompilationManager.ResolvedDocument;
        } catch (OperationCanceledException) {
        }
        return state.Observer.LastPublishedDocument;
      }
      return null;
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
