using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive.Concurrency;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Runtime.Caching;
using System.Threading;
using System.Threading.Tasks;
using IntervalTree;
using MediatR;
using Microsoft.Dafny.LanguageServer.Language;
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
  public Compilation Compilation { get; private set; }
  private IDisposable observerSubscription;
  private readonly ILogger<DocumentManager> logger;

  private bool VerifyOnOpen => options.Get(ServerCommand.Verification) == VerifyOnMode.Change;
  private bool VerifyOnChange => options.Get(ServerCommand.Verification) == VerifyOnMode.Change;
  private bool VerifyOnSave => options.Get(ServerCommand.Verification) == VerifyOnMode.Save;
  public List<Position> ChangedVerifiables { get; set; } = new();
  public List<Range> ChangedRanges { get; set; } = new();

  private readonly SemaphoreSlim workCompletedForCurrentVersion = new(0);
  private readonly DafnyOptions options;
  private readonly IScheduler updateScheduler = new EventLoopScheduler();

  public DocumentManager(
    IServiceProvider services,
    DocumentTextBuffer document) {
    this.services = services;
    this.options = services.GetRequiredService<DafnyOptions>();
    this.logger = services.GetRequiredService<ILogger<DocumentManager>>();
    this.relocator = services.GetRequiredService<IRelocator>();
    this.textChangeProcessor = services.GetRequiredService<ITextChangeProcessor>();

    observer = new IdeStateObserver(services.GetRequiredService<ILogger<IdeStateObserver>>(),
      services.GetRequiredService<ITelemetryPublisher>(),
      services.GetRequiredService<INotificationPublisher>(),
      services.GetRequiredService<ITextDocumentLoader>(),
      document);
    Compilation = new Compilation(
      services,
      DetermineDocumentOptions(options, document.Uri),
      document,
      null);

    observerSubscription = Compilation.DocumentUpdates.Select(d => d.InitialIdeState(options)).Subscribe(observer);
    changeReceived.Throttle(TimeSpan.FromMilliseconds(20)).ObserveOn(updateScheduler)
      .Subscribe(_ => ProcessChanges());
    var _ = Task.Run(() => {

      if (VerifyOnOpen) {
        var _ = VerifyEverythingAsync();
      } else {
        // logger.LogDebug("Setting result for workCompletedForCurrentVersion");
        workCompletedForCurrentVersion.Release();
      }

      Compilation.Start();
    });
  }

  private const int MaxRememberedChanges = 100;
  private const int MaxRememberedChangedVerifiables = 5;

  private readonly ConcurrentQueue<DidChangeTextDocumentParams> changeRequests = new();
  private readonly object changeLock = new();
  void ProcessChanges() {
    lock (changeLock) {
      var items = new List<DidChangeTextDocumentParams>(changeRequests.Count);
      while (!changeRequests.IsEmpty) {
        if (changeRequests.TryDequeue(out var change)) {
          items.Add(change);
        }
      }

      if (items.Count == 0) {
        return;
      }
      var changes = items.SelectMany(cr => cr.ContentChanges).ToList();
      var document = items[^1].TextDocument;
      logger.LogError($"Merged {items.Count} items");
      var merged = new DidChangeTextDocumentParams() {
        TextDocument = document,
        ContentChanges = changes
      };
      ProcessDocumentChange(merged);
    }
  }

  private readonly Subject<Unit> changeReceived = new();
  /// <summary>
  /// In this method it's important to reach oldCompilation.CancelPendingUpdates soon, to prevent doing stale work.
  /// </summary>
  /// <param name="documentChange"></param>
  /// <exception cref="InvalidOperationException"></exception>
  public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
    Compilation.CancelPendingUpdates();
    changeRequests.Enqueue(documentChange);
    changeReceived.OnNext(Unit.Value);
  }

  private void ProcessDocumentChange(DidChangeTextDocumentParams documentChange) {
    // According to the LSP specification, document versions should increase monotonically but may be non-consecutive.
    // See: https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/specification-3-16.md?plain=1#L1195
    var oldVer = Compilation.TextBuffer.Version;
    var newVer = documentChange.TextDocument.Version;
    var documentUri = documentChange.TextDocument.Uri;
    if (oldVer >= newVer) {
      throw new InvalidOperationException(
        $"the updates of document {documentUri} are out-of-order: {oldVer} -> {newVer}");
    }

    var _1 = workCompletedForCurrentVersion.WaitAsync();

    var before = DateTime.Now;
    var updatedText = textChangeProcessor.ApplyChange(Compilation.TextBuffer, documentChange, CancellationToken.None);
    logger.LogError($"Applying text change took {(DateTime.Now - before).Milliseconds}ms");

    var lastPublishedState = observer.LastPublishedState;

    var changeProcessor = relocator.GetChangeProcessor(documentChange, CancellationToken.None);
    var migratedVerificationTree =
      changeProcessor.RelocateVerificationTree(lastPublishedState.VerificationTree, updatedText.NumberOfLines);

    var dafnyOptions = GetDocumentOptions(documentChange);
    Compilation = new Compilation(
      services,
      dafnyOptions,
      updatedText,
      // TODO do not pass this to CompilationManager but instead use it in FillMissingStateUsingLastPublishedDocument
      // This will improve cancellation hits since UpdateDocument will complete faster since it does less migration
      migratedVerificationTree
    );
    var afterCancel = DateTime.Now;

    lock (ChangedRanges) {
      ChangedRanges = documentChange.ContentChanges.Select(contentChange => contentChange.Range).Concat(
          ChangedRanges.Select(range => changeProcessor.MigrateRange(range))).Where(r => r != null)
        .Take(MaxRememberedChanges).ToList()!;
    }
    if (VerifyOnChange) {
      var _ = VerifyEverythingAsync();
    } else {
      workCompletedForCurrentVersion.Release();
    }

    observerSubscription.Dispose();
    var migratedLastPublishedState = lastPublishedState with {
      ImplementationIdToView = MigrateImplementationViews(changeProcessor, lastPublishedState.ImplementationIdToView),
      SignatureAndCompletionTable = changeProcessor.MigrateSymbolTable(lastPublishedState.SignatureAndCompletionTable),
      VerificationTree = migratedVerificationTree
    };
    var migratedUpdates = Compilation.DocumentUpdates.Select(document =>
      document.ToIdeState(migratedLastPublishedState));
    observerSubscription = migratedUpdates.Subscribe(observer);
    Compilation.Start();
  }

  private DafnyOptions GetDocumentOptions(DidChangeTextDocumentParams documentChange) {
    var cacheKey = documentChange.TextDocument.Uri.ToUri().AbsoluteUri;
    var result = memoryCache.Get(cacheKey) as DafnyOptions;
    if (result == null) {
      result = DetermineDocumentOptions(options, documentChange.TextDocument.Uri);
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
    Compilation.CancelPendingUpdates();
    try {
      await Compilation.LastDocument;
    } catch (TaskCanceledException) {
    }
  }

  public async Task<DocumentAfterParsing> GetLastDocumentAsync() {
    await workCompletedForCurrentVersion.WaitAsync();
    workCompletedForCurrentVersion.Release();
    return await Compilation.LastDocument;
  }

  public async Task<IdeState> GetSnapshotAfterResolutionAsync() {
    try {
      var resolvedDocument = await Compilation.ResolvedDocument;
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

  private async Task VerifyEverythingAsync() {
    try {
      var translatedDocument = await Compilation.TranslatedDocument;

      var implementationTasks = translatedDocument.VerificationTasks;

      if (!implementationTasks.Any()) {
        Compilation.FinishedNotifications(translatedDocument);
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
        Compilation.VerifyTask(translatedDocument, implementationTask);
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
