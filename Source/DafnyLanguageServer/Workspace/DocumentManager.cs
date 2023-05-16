using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive.Concurrency;
using System.Reactive.Disposables;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Reactive.Threading.Tasks;
using System.Runtime.Caching;
using System.Threading;
using System.Threading.Tasks;
using IntervalTree;
using MediatR;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

/// <summary>
/// Handles operation on a single document.
/// Handles migration of previously published document state
/// </summary>
public class DocumentManager {
  private MemoryCache memoryCache = MemoryCache.Default;
  private readonly IRelocator relocator;
  private readonly ITextChangeProcessor textChangeProcessor;

  private readonly IServiceProvider services;
  private readonly IdeStateObserver observer;
  private TaskCompletionSource<Compilation> compilationSource = new();
  public Task<Compilation> Compilation => compilationSource.Task;
  private IDisposable observerSubscription;
  private readonly ILogger<DocumentManager> logger;

  private bool VerifyOnOpen => options.Get(ServerCommand.Verification) == VerifyOnMode.Change;
  private bool VerifyOnChange => options.Get(ServerCommand.Verification) == VerifyOnMode.Change;
  private bool VerifyOnSave => options.Get(ServerCommand.Verification) == VerifyOnMode.Save;
  public List<Position> ChangedVerifiables { get; set; } = new();
  public List<Range> ChangedRanges { get; set; } = new();

  private readonly SemaphoreSlim workCompletedForCurrentVersion = new(1);
  private readonly DafnyOptions options;
  private readonly IScheduler updateScheduler = new EventLoopScheduler();
  private CancellationTokenSource cancellationTokenSource;
  private DocumentTextBuffer document;

  public DocumentManager(
    IServiceProvider services,
    DocumentTextBuffer document) {
    this.services = services;
    this.options = services.GetRequiredService<DafnyOptions>();
    this.logger = services.GetRequiredService<ILogger<DocumentManager>>();
    this.relocator = services.GetRequiredService<IRelocator>();
    this.textChangeProcessor = services.GetRequiredService<ITextChangeProcessor>();

    this.document = document;
    observer = new IdeStateObserver(services.GetRequiredService<ILogger<IdeStateObserver>>(),
      services.GetRequiredService<ITelemetryPublisher>(),
      services.GetRequiredService<INotificationPublisher>(),
      services.GetRequiredService<ITextDocumentLoader>(),
      document);
    cancellationTokenSource = new();

    changeReceived.Throttle(TimeSpan.FromMilliseconds(20)).ObserveOn(updateScheduler)
      .Subscribe(_ => ProcessChanges());

    var initialIdeState = new IdeState(document, Array.Empty<Diagnostic>(),
      SymbolTable.Empty(), SignatureAndCompletionTable.Empty(options, document),
      new Dictionary<ImplementationId, IdeImplementationView>(),
      Array.Empty<Counterexample>(),
      false, Array.Empty<Diagnostic>(),
      new DocumentVerificationTree(document));

    observerSubscription = Disposable.Empty;
    var _ = Task.Run(() => {
      CreateAndStartCompilation(compilationSource, initialIdeState, VerifyOnOpen);
    });
  }

  private const int MaxRememberedChanges = 100;
  private const int MaxRememberedChangedVerifiables = 5;

  private readonly ConcurrentQueue<(DidChangeTextDocumentParams, TaskCompletionSource<Compilation>)> changeRequests = new();
  private readonly object changeLock = new();
  void ProcessChanges() {
    lock (changeLock) {
      var items = new List<DidChangeTextDocumentParams>(changeRequests.Count);
      TaskCompletionSource<Compilation> compilationSource = null!;
      while (!changeRequests.IsEmpty) {
        if (changeRequests.TryDequeue(out var change)) {
          items.Add(change.Item1);
          compilationSource = change.Item2;
        }
      }

      if (items.Count == 0) {
        return;
      }
      var changes = items.SelectMany(cr => cr.ContentChanges).ToList();
      var documentIdentifier = items[^1].TextDocument;
      logger.LogError($"Merged {items.Count} items");
      var merged = new DidChangeTextDocumentParams {
        TextDocument = documentIdentifier,
        ContentChanges = changes
      };
      ProcessDocumentChange(compilationSource!, merged);
    }
  }

  private readonly Subject<Unit> changeReceived = new();
  /// <summary>
  /// In this method it's important to reach oldCompilation.CancelPendingUpdates soon, to prevent doing stale work.
  /// </summary>
  /// <param name="documentChange"></param>
  /// <exception cref="InvalidOperationException"></exception>
  public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
    cancellationTokenSource.Cancel();
    cancellationTokenSource = new();
    // There's a race condition here with ProcessDocumentChange. Should add a lock
    compilationSource = new();
    changeRequests.Enqueue((documentChange, compilationSource));
    changeReceived.OnNext(Unit.Value);
  }

  private void ProcessDocumentChange(TaskCompletionSource<Compilation> compilationSource, DidChangeTextDocumentParams documentChange) {
    // According to the LSP specification, document versions should increase monotonically but may be non-consecutive.
    // See: https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/specification-3-16.md?plain=1#L1195
    var oldVer = document.Version;
    var newVer = documentChange.TextDocument.Version;
    var documentUri = documentChange.TextDocument.Uri;
    if (oldVer >= newVer) {
      throw new InvalidOperationException(
        $"the updates of document {documentUri} are out-of-order: {oldVer} -> {newVer}");
    }

    var before = DateTime.Now;
    document = textChangeProcessor.ApplyChange(document, documentChange, CancellationToken.None);
    logger.LogError($"Applying text change took {(DateTime.Now - before).Milliseconds}ms");

    var lastPublishedState = observer.LastPublishedState;

    var changeProcessor = relocator.GetChangeProcessor(documentChange, CancellationToken.None);
    var migratedVerificationTree =
      changeProcessor.RelocateVerificationTree(lastPublishedState.VerificationTree, document.NumberOfLines);

    lock (ChangedRanges) {
      ChangedRanges = documentChange.ContentChanges.Select(contentChange => contentChange.Range).Concat(
          ChangedRanges.Select(range => changeProcessor.MigrateRange(range))).Where(r => r != null)
        .Take(MaxRememberedChanges).ToList()!;
    }
    observerSubscription.Dispose();

    observer.LastPublishedState = lastPublishedState with {
      ImplementationIdToView = MigrateImplementationViews(changeProcessor, lastPublishedState.ImplementationIdToView),
      SignatureAndCompletionTable = changeProcessor.MigrateSymbolTable(lastPublishedState.SignatureAndCompletionTable),
      VerificationTree = migratedVerificationTree
    };
    CreateAndStartCompilation(compilationSource, observer.LastPublishedState, VerifyOnChange);
  }

  private void CreateAndStartCompilation(TaskCompletionSource<Compilation> compilationSource,
    IdeState lastIdeState,
    bool verifyEverything) {

    var _1 = workCompletedForCurrentVersion.WaitAsync();
    var compilation = new Compilation(
      services,
      GetDocumentOptions(document.Uri),
      document,
      lastIdeState.VerificationTree, cancellationTokenSource.Token);

    if (!compilationSource.TrySetResult(compilation)) {
      return;
    }

    observerSubscription = compilation.DocumentUpdates.Select(d => d.ToIdeState(lastIdeState)).Subscribe(observer);

    if (verifyEverything) {
      var _ = VerifyEverythingAsync();
    } else {
      workCompletedForCurrentVersion.Release();
    }

    compilation.Start();
  }

  private DafnyOptions GetDocumentOptions(TextDocumentIdentifier textDocument) {
    var cacheKey = textDocument.Uri.ToUri().AbsoluteUri;
    var result = memoryCache.Get(cacheKey) as DafnyOptions;
    if (result == null) {
      result = DetermineDocumentOptions(options, textDocument.Uri);
      memoryCache.Set(new CacheItem(cacheKey, result), new CacheItemPolicy {
        SlidingExpiration = new TimeSpan(0, 0, 5)
      });
    }
    return result;
  }

  private static DafnyOptions DetermineDocumentOptions(DafnyOptions serverOptions, DocumentUri uri) {
    ProjectFile? projectFile = null;

    var folder = Path.GetDirectoryName(uri.GetFileSystemPath());
    while (!string.IsNullOrEmpty(folder)) {
      var children = Directory.GetFiles(folder, "dfyconfig.toml");
      if (children.Length > 0) {
        var errorWriter = TextWriter.Null;
        projectFile = ProjectFile.Open(new Uri(children[0]), errorWriter);
        if (projectFile != null) {
          break;
        }
      }
      folder = Path.GetDirectoryName(folder);
    }

    if (projectFile != null) {
      var result = new DafnyOptions(serverOptions);

      foreach (var option in ServerCommand.Instance.Options) {
        object? projectFileValue = null;
        var hasProjectFileValue = projectFile?.TryGetValue(option, TextWriter.Null, out projectFileValue) ?? false;
        if (hasProjectFileValue) {
          result.Options.OptionArguments[option] = projectFileValue;
          result.ApplyBinding(option);
        }
      }

      return result;
    }

    return serverOptions;
  }

  private Dictionary<ImplementationId, IdeImplementationView> MigrateImplementationViews(ChangeProcessor changeProcessor,
    IReadOnlyDictionary<ImplementationId, IdeImplementationView> oldVerificationDiagnostics) {
    var result = new Dictionary<ImplementationId, IdeImplementationView>();
    foreach (var entry in oldVerificationDiagnostics) {
      var newRange = changeProcessor.MigrateRange(entry.Value.Range);
      if (newRange != null) {
        result.Add(entry.Key with {
          NamedVerificationTask = changeProcessor.MigratePosition(entry.Key.NamedVerificationTask)
        }, entry.Value with {
          Range = newRange,
          Diagnostics = changeProcessor.MigrateDiagnostics(entry.Value.Diagnostics)
        });
      }
    }
    return result;
  }

  public void Save() {
    if (VerifyOnSave) {
      logger.LogDebug("Clearing result for workCompletedForCurrentVersion");
      var _1 = workCompletedForCurrentVersion.WaitAsync();
      var _2 = VerifyEverythingAsync();
    }
  }

  public async Task CloseAsync() {
    cancellationTokenSource.Cancel();
    try {
      var compilation = await Compilation;
      await compilation.LastDocument;
    } catch (TaskCanceledException) {
    }
  }

  public async Task<DocumentAfterParsing> GetLastDocumentAsync() {
    await workCompletedForCurrentVersion.WaitAsync();
    workCompletedForCurrentVersion.Release();
    var compilation = await Compilation;
    return await compilation.LastDocument;
  }

  public async Task<IdeState> GetSnapshotAfterResolutionAsync() {
    try {
      var compilation = await Compilation;
      var resolvedDocument = await compilation.ResolvedDocument;
      logger.LogDebug($"GetSnapshotAfterResolutionAsync, resolvedDocument.Version = {resolvedDocument.Version}, " +
                      $"observer.LastPublishedState.Version = {observer.LastPublishedState.Version}, threadId: {Thread.CurrentThread.ManagedThreadId}");
    } catch (OperationCanceledException) {
      logger.LogDebug("Caught OperationCanceledException in GetSnapshotAfterResolutionAsync");
    }

    return observer.LastPublishedState;
  }

  public async Task<IdeState> GetIdeStateAfterVerificationAsync() {
    try {
      await GetLastDocumentAsync();
    } catch (OperationCanceledException) {
    }

    return observer.LastPublishedState;
  }

  private int counter = 0;
  private async Task VerifyEverythingAsync() {
    var count = counter++;
    try {
      // Will this compilation always include the latest received edits? I think so, because compilationSource is cleared when an edit is received 
      var compilation = await Compilation;
      var translatedDocument = await compilation.TranslatedDocument;

      var implementationTasks = translatedDocument.VerificationTasks;

      if (!implementationTasks.Any()) {
        compilation.FinishedNotifications(translatedDocument);
      }

      lock (ChangedRanges) {
        var freshlyChangedVerifiables = GetChangedVerifiablesFromRanges(translatedDocument, ChangedRanges);
        ChangedVerifiables = freshlyChangedVerifiables.Concat(ChangedVerifiables).Distinct()
          .Take(MaxRememberedChangedVerifiables).ToList();
        ChangedRanges = new List<Range>();
      }

      var implementationOrder = ChangedVerifiables.Select((v, i) => (v, i)).ToDictionary(k => k.v, k => k.i);
      var orderedTasks = implementationTasks.OrderBy(t => t.Implementation.Priority).CreateOrderedEnumerable(
        t => implementationOrder.GetOrDefault(t.Implementation.tok.GetLspPosition(), () => int.MaxValue),
        null, false).ToList();

      foreach (var implementationTask in orderedTasks) {
        compilation.VerifyTask(translatedDocument, implementationTask);
      }
    }
    finally {
      logger.LogDebug("Setting result for workCompletedForCurrentVersion");
      workCompletedForCurrentVersion.Release();
    }
  }

  private IEnumerable<Position> GetChangedVerifiablesFromRanges(DocumentAfterResolution loaded, IEnumerable<Range> changedRanges) {
    var tree = new DocumentVerificationTree(loaded.TextDocumentItem);
    VerificationProgressReporter.UpdateTree(options, loaded, tree);
    var intervalTree = new IntervalTree<Position, Position>();
    foreach (var childTree in tree.Children) {
      intervalTree.Add(childTree.Range.Start, childTree.Range.End, childTree.Position);
    }

    return changedRanges.SelectMany(changeRange => intervalTree.Query(changeRange.Start, changeRange.End));
  }
}
