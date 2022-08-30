using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Linq;
using System.Threading;
using System.Threading.Tasks;
using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

/// <summary>
/// Handles operation on a single document.
/// Handles migration of previously published document state
/// </summary>
public class DocumentManager {
  private readonly IRelocator relocator;
  private readonly ITextChangeProcessor textChangeProcessor;

  private readonly IServiceProvider services;
  private readonly DocumentOptions documentOptions;
  private readonly VerifierOptions verifierOptions;
  private readonly DocumentObserver observer;
  public Compilation Compilation { get; private set; }
  private IDisposable observerSubscription;

  private bool VerifyOnOpen => documentOptions.Verify == AutoVerification.OnChange;
  private bool VerifyOnChange => documentOptions.Verify == AutoVerification.OnChange;
  private bool VerifyOnSave => documentOptions.Verify == AutoVerification.OnSave;
  public List<Position> ChangedVerifiables { get; set; } = new();
  public List<Range> ChangedRanges { get; set; } = new();
  public Task<DocumentAfterParsing> LastDocumentAsync => Compilation.LastDocument;

  public DocumentManager(
    IServiceProvider services,
    DocumentOptions documentOptions,
    VerifierOptions verifierOptions,
    DocumentTextBuffer document) {
    this.services = services;
    this.documentOptions = documentOptions;
    this.verifierOptions = verifierOptions;
    this.relocator = services.GetRequiredService<IRelocator>();
    this.textChangeProcessor = services.GetRequiredService<ITextChangeProcessor>();

    observer = new DocumentObserver(services.GetRequiredService<ILogger<DocumentObserver>>(),
      services.GetRequiredService<ITelemetryPublisher>(),
      services.GetRequiredService<INotificationPublisher>(),
      services.GetRequiredService<ITextDocumentLoader>(),
      document);
    Compilation = new Compilation(
      services,
      verifierOptions,
      document,
      null);

    if (VerifyOnOpen) {
      var _ = VerifyEverythingAsync();
    } else {
      Compilation.MarkVerificationFinished();
    }

    observerSubscription = Compilation.DocumentUpdates.Select(d => d.InitialIdeState()).Subscribe(observer);
  }

  private const int MaxRememberedChanges = 100;
  private const int MaxRememberedChangedVerifiables = 5;
  public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
    // According to the LSP specification, document versions should increase monotonically but may be non-consecutive.
    // See: https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/specification-3-16.md?plain=1#L1195
    var oldVer = Compilation.TextBuffer.Version;
    var newVer = documentChange.TextDocument.Version;
    var documentUri = documentChange.TextDocument.Uri;
    if (oldVer >= newVer) {
      throw new InvalidOperationException(
        $"the updates of document {documentUri} are out-of-order: {oldVer} -> {newVer}");
    }

    Compilation.CancelPendingUpdates();
    var updatedText = textChangeProcessor.ApplyChange(Compilation.TextBuffer, documentChange, CancellationToken.None);

    var lastPublishedState = observer.LastPublishedState;
    lastPublishedState = lastPublishedState with {
      ImplementationIdToView = MigrateImplementationViews(documentChange, lastPublishedState.ImplementationIdToView),
      SymbolTable = relocator.RelocateSymbols(lastPublishedState.SymbolTable, documentChange, CancellationToken.None)
    };

    lock (ChangedRanges) {
      ChangedRanges = documentChange.ContentChanges.Select(contentChange => contentChange.Range).Concat(
        ChangedRanges.Select(range =>
            relocator.RelocateRange(range, documentChange, CancellationToken.None))).
          Where(r => r != null).Take(MaxRememberedChanges).ToList()!;
    }

    var migratedVerificationTree =
      relocator.RelocateVerificationTree(lastPublishedState.VerificationTree, updatedText.NumberOfLines, documentChange, CancellationToken.None);

    Compilation = new Compilation(
      services,
      verifierOptions,
      updatedText,
      // TODO do not pass this to CompilationManager but instead use it in FillMissingStateUsingLastPublishedDocument
      migratedVerificationTree
    );

    if (VerifyOnChange) {
      var _ = VerifyEverythingAsync();
    } else {
      Compilation.MarkVerificationFinished();
    }

    observerSubscription.Dispose();
    var migratedUpdates = Compilation.DocumentUpdates.Select(document =>
      document.ToIdeState(lastPublishedState));
    observerSubscription = migratedUpdates.Subscribe(observer);
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
      Compilation.MarkVerificationStarted();
      var _ = VerifyEverythingAsync();
    }
  }

  public async Task CloseAsync() {
    Compilation.CancelPendingUpdates();
    try {
      await Compilation.LastDocument;
    } catch (TaskCanceledException) {
    }
  }

  public async Task<IdeState> GetSnapshotAfterResolutionAsync() {
    try {
      await Compilation.ResolvedDocument;
    } catch (OperationCanceledException) {
    }

    return observer.LastPublishedState;
  }

  public async Task<IdeState> GetIdeStateAfterVerificationAsync() {
    try {
      await Compilation.LastDocument;
    } catch (OperationCanceledException) {
    }

    return observer.LastPublishedState;
  }

  private async Task VerifyEverythingAsync() {
    var translatedDocument = await Compilation.TranslatedDocument;

    var implementationTasks = translatedDocument.VerificationTasks;

    if (!implementationTasks.Any()) {
      Compilation.FinishedNotifications(translatedDocument);
    }

    lock (ChangedRanges) {
      var freshlyChangedVerifiables = GetChangedVerifiablesFromRanges(translatedDocument, ChangedRanges);
      ChangedVerifiables = freshlyChangedVerifiables.Concat(ChangedVerifiables).Distinct().Take(MaxRememberedChangedVerifiables).ToList();
      ChangedRanges = new List<Range>();
    }

    var implementationOrder = ChangedVerifiables.Select((v, i) => (v, i)).ToDictionary(k => k.v, k => k.i);
    var orderedTasks = implementationTasks.
      OrderBy(t => t.Implementation.Priority).
      CreateOrderedEnumerable(
        t => implementationOrder.GetOrDefault(t.Implementation.tok.GetLspPosition(), () => int.MaxValue),
        null, false).
      ToList();

    foreach (var implementationTask in orderedTasks) {
      Compilation.VerifyTask(translatedDocument, implementationTask);
    }
  }

  private IEnumerable<Position> GetChangedVerifiablesFromRanges(DocumentAfterResolution loaded, IEnumerable<Range> changedRanges) {
    var tree = new DocumentVerificationTree(loaded.TextDocumentItem);
    VerificationProgressReporter.UpdateTree(loaded, tree);
    var intervalTree = new IntervalTree<Position, Position>();
    foreach (var childTree in tree.Children) {
      intervalTree.Add(childTree.Range.Start, childTree.Range.End, childTree.Position);
    }

    return changedRanges.SelectMany(changeRange => intervalTree.Query(changeRange.Start, changeRange.End));
  }
}
