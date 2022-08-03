using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

/// <summary>
/// Handles operation on a single document.
/// Handles migration of previously published document state
/// </summary>
public class DocumentManager {
  private readonly IRelocator relocator;
  private readonly ITextChangeProcessor textChangeProcessor;
  private readonly INotificationPublisher notificationPublisher;

  private readonly IServiceProvider services;
  private readonly DocumentOptions documentOptions;
  private readonly VerifierOptions verifierOptions;
  private readonly DocumentObserver observer;
  public CompilationManager CompilationManager { get; private set; }
  private IDisposable observerSubscription;

  private bool VerifyOnOpen => documentOptions.Verify == AutoVerification.OnChange;
  private bool VerifyOnChange => documentOptions.Verify == AutoVerification.OnChange;
  private bool VerifyOnSave => documentOptions.Verify == AutoVerification.OnSave;
  public Task<DafnyDocument> LastDocumentAsync => CompilationManager.LastDocument;

  public DocumentManager(
    IServiceProvider services,
    DocumentOptions documentOptions,
    VerifierOptions verifierOptions,
    DocumentTextBuffer document) {
    this.services = services;
    this.documentOptions = documentOptions;
    this.verifierOptions = verifierOptions;
    this.relocator = services.GetRequiredService<IRelocator>();
    this.notificationPublisher = services.GetRequiredService<INotificationPublisher>();
    this.textChangeProcessor = services.GetRequiredService<ITextChangeProcessor>();

    observer = new DocumentObserver(services.GetRequiredService<ILogger<DocumentObserver>>(),
      services.GetRequiredService<ITelemetryPublisher>(),
      services.GetRequiredService<INotificationPublisher>(),
      services.GetRequiredService<ITextDocumentLoader>(),
      document);
    CompilationManager = new CompilationManager(services,
      verifierOptions,
      document,
      null,
      VerifyOnOpen,
      ImmutableList.Create<Position>(),
      null);
    observerSubscription = CompilationManager.DocumentUpdates.Subscribe(observer);
  }

  public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
    // According to the LSP specification, document versions should increase monotonically but may be non-consecutive.
    // See: https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/specification-3-16.md?plain=1#L1195
    var oldVer = CompilationManager.TextBuffer.Version;
    var newVer = documentChange.TextDocument.Version;
    var documentUri = documentChange.TextDocument.Uri;
    if (oldVer >= newVer) {
      throw new InvalidOperationException(
        $"the updates of document {documentUri} are out-of-order: {oldVer} -> {newVer}");
    }

    CompilationManager.CancelPendingUpdates();
    var updatedText = textChangeProcessor.ApplyChange(CompilationManager.TextBuffer, documentChange, CancellationToken.None);

    var lastPublishedDocument = observer.LastPublishedDocument;
    var oldVerificationDiagnostics = lastPublishedDocument.ImplementationIdToView;
    var migratedImplementationViews =
      oldVerificationDiagnostics == null ? null : MigrateImplementationViews(documentChange, oldVerificationDiagnostics);

    // TODO it would be simpler to store last touched positions at the DocumentState level, and always recompute the lastTouchedVerifiables from that.
    // Then we don't need to touch lastPublishedDocument.LastTouchedVerifiables which seems unreliable.
    var migratedLastTouchedVerifiables =
      relocator.RelocatePositions(lastPublishedDocument.LastTouchedVerifiables, documentChange, CancellationToken.None);

    var migratedVerificationTree =
      relocator.RelocateVerificationTree(lastPublishedDocument.VerificationTree, updatedText.NumberOfLines, documentChange, CancellationToken.None);

    var lastChange = documentChange.ContentChanges.Select(contentChange => contentChange.Range).LastOrDefault();

    CompilationManager = new CompilationManager(
      services,
      verifierOptions,
      updatedText,
      lastChange,
      VerifyOnChange,
      migratedLastTouchedVerifiables,
      // TODO do not pass this to CompilationManager but instead use it in FillMissingStateUsingLastPublishedDocument
      migratedVerificationTree
    );

    observerSubscription.Dispose();
    var migratedUpdates = CompilationManager.DocumentUpdates.Select(document =>
      FillMissingStateUsingLastPublishedDocument(documentChange, document, lastPublishedDocument, migratedImplementationViews));
    observerSubscription = migratedUpdates.Subscribe(observer);
  }

  private DafnyDocument FillMissingStateUsingLastPublishedDocument(DidChangeTextDocumentParams documentChange,
    DafnyDocument document, DafnyDocument lastPublishedDocument,
    IReadOnlyDictionary<ImplementationId, ImplementationView>? migratedImplementationViews) {
    if (!document.SymbolTable.Resolved) {
      document = document with {
        SymbolTable =
        relocator.RelocateSymbols(lastPublishedDocument.SymbolTable, documentChange, CancellationToken.None)
      };
    }

    var migratedViews = document.ImplementationIdToView?.Select(kv => {
      var value = kv.Value.Status < PublishedVerificationStatus.Error
        ? kv.Value with {
          Diagnostics = migratedImplementationViews?.GetValueOrDefault(kv.Key)?.Diagnostics ?? kv.Value.Diagnostics
        }
        : kv.Value;
      return new KeyValuePair<ImplementationId, ImplementationView>(kv.Key, value);
    }) ?? migratedImplementationViews;
    document.ImplementationIdToView = migratedViews == null ? null : new(migratedViews);

    return document;
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

  public void Save() {
    if (VerifyOnSave) {
      CompilationManager.Verify();
    }
  }

  public async Task CloseAsync() {
    CompilationManager.CancelPendingUpdates();
    try {
      await CompilationManager.LastDocument;
    } catch (TaskCanceledException) {
    }
  }

  /// <summary>
  /// Tries to resolve the current document and return it, and otherwise return the last document that was resolved.
  /// </summary>
  public async Task<DafnyDocument?> GetResolvedDocumentAsync() {
    try {
      var resolvedDocument = await CompilationManager.ResolvedDocument;
    } catch (OperationCanceledException) {
    }

    var result = observer.LastPublishedDocument;
    return result;
  }
}