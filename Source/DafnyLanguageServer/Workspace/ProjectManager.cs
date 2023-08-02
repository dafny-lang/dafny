using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Reactive.Disposables;
using System.Reactive.Linq;
using System.Threading;
using System.Threading.Tasks;
using IntervalTree;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

using VerifyStatus = Dictionary<string, (IImplementationTask Task, ImplementationView View)>;

public delegate ProjectManager CreateProjectManager(
  ExecutionEngine boogieEngine,
  DafnyProject project);

public record FilePosition(Uri Uri, Position Position);

/// <summary>
/// Handles operation on a single document.
/// Handles migration of previously published document state
/// </summary>
public class ProjectManager : IDisposable {
  private readonly IRelocator relocator;
  public DafnyProject Project { get; }

  private readonly IdeStateObserver observer;
  public CompilationManager CompilationManager { get; private set; }
  private IDisposable observerSubscription;
  private readonly INotificationPublisher notificationPublisher;
  private readonly IVerificationProgressReporter verificationProgressReporter;
  private readonly ILogger<ProjectManager> logger;

  /// <summary>
  /// The version of this project.
  /// Is incremented when any file in the project is updated.
  /// Is used as part of project-wide notifications.
  /// Can be used by the client to ignore outdated notifications
  /// </summary>
  private int version;

  private int openFileCount;

  private bool VerifyOnOpenChange => options.Get(ServerCommand.Verification) == VerifyOnMode.Change;
  private bool VerifyOnSave => options.Get(ServerCommand.Verification) == VerifyOnMode.Save;
  public List<FilePosition> ChangedVerifiables { get; set; } = new();
  public List<Location> RecentChanges { get; set; } = new();

  private readonly SemaphoreSlim workCompletedForCurrentVersion = new(1);
  private readonly DafnyOptions options;
  private readonly DafnyOptions serverOptions;
  private readonly CreateCompilationManager createCompilationManager;
  private readonly ExecutionEngine boogieEngine;
  private readonly IFileSystem fileSystem;

  public ProjectManager(
    DafnyOptions serverOptions,
    ILogger<ProjectManager> logger,
    IRelocator relocator,
    IFileSystem fileSystem,
    INotificationPublisher notificationPublisher,
    IVerificationProgressReporter verificationProgressReporter,
    CreateCompilationManager createCompilationManager,
    CreateIdeStateObserver createIdeStateObserver,
    ExecutionEngine boogieEngine,
    DafnyProject project) {
    Project = project;
    this.verificationProgressReporter = verificationProgressReporter;
    this.notificationPublisher = notificationPublisher;
    this.serverOptions = serverOptions;
    this.fileSystem = fileSystem;
    this.createCompilationManager = createCompilationManager;
    this.relocator = relocator;
    this.logger = logger;
    this.boogieEngine = boogieEngine;

    options = DetermineProjectOptions(project, serverOptions);
    options.Printer = new OutputLogger(logger);

    var initialCompilation = CreateInitialCompilation();
    observer = createIdeStateObserver(initialCompilation);
    CompilationManager = createCompilationManager(
        options, boogieEngine, initialCompilation, ImmutableDictionary<Uri, VerificationTree>.Empty
    );

    observerSubscription = Disposable.Empty;
  }

  private Compilation CreateInitialCompilation() {
    var rootUris = Project.GetRootSourceUris(fileSystem).Concat(options.CliRootSourceUris).ToList();
    return new Compilation(version, Project, rootUris);
  }

  private const int MaxRememberedChanges = 100;
  private const int MaxRememberedChangedVerifiables = 5;

  public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
    var lastPublishedState = observer.LastPublishedState;
    var migratedVerificationTrees = lastPublishedState.VerificationTrees.ToDictionary(
      kv => kv.Key, kv =>
      relocator.RelocateVerificationTree(kv.Value, documentChange, CancellationToken.None));
    lastPublishedState = lastPublishedState with {
      ImplementationViews = MigrateImplementationViews(documentChange, lastPublishedState.ImplementationViews),
      SignatureAndCompletionTable = relocator.RelocateSymbols(lastPublishedState.SignatureAndCompletionTable, documentChange, CancellationToken.None),
      VerificationTrees = migratedVerificationTrees
    };

    lock (RecentChanges) {
      var newChanges = documentChange.ContentChanges.Where(c => c.Range != null).
        Select(contentChange => new Location {
          Range = contentChange.Range!,
          Uri = documentChange.TextDocument.Uri
        });
      var migratedChanges = RecentChanges.Select(location => {
        var newRange = relocator.RelocateRange(location.Range, documentChange, CancellationToken.None);
        if (newRange == null) {
          return null;
        }
        return new Location {
          Range = newRange,
          Uri = location.Uri
        };
      }).Where(r => r != null);
      RecentChanges = newChanges.Concat(migratedChanges).Take(MaxRememberedChanges).ToList()!;
    }

    StartNewCompilation(migratedVerificationTrees, lastPublishedState);
    TriggerVerificationForFile(documentChange.TextDocument.Uri.ToUri());
  }

  private void StartNewCompilation(IReadOnlyDictionary<Uri, VerificationTree> migratedVerificationTrees,
    IdeState lastPublishedState) {
    version++;
    logger.LogDebug("Clearing result for workCompletedForCurrentVersion");


    CompilationManager.CancelPendingUpdates();
    CompilationManager = createCompilationManager(
      options,
      boogieEngine,
      CreateInitialCompilation(),
      migratedVerificationTrees);

    observerSubscription.Dispose();
    var migratedUpdates = CompilationManager.CompilationUpdates.Select(document =>
      document.ToIdeState(lastPublishedState));
    observerSubscription = migratedUpdates.Subscribe(observer);

    CompilationManager.Start();
  }

  public void TriggerVerificationForFile(Uri triggeringFile) {
    if (VerifyOnOpenChange) {
      var _ = VerifyEverythingAsync(null);
    } else {
      logger.LogDebug("Setting result for workCompletedForCurrentVersion");
    }
  }

  private static DafnyOptions DetermineProjectOptions(DafnyProject projectOptions, DafnyOptions serverOptions) {
    var result = new DafnyOptions(serverOptions);

    foreach (var option in ServerCommand.Instance.Options) {
      var hasProjectFileValue = projectOptions.TryGetValue(option, TextWriter.Null, out var projectFileValue);
      if (hasProjectFileValue) {
        result.Options.OptionArguments[option] = projectFileValue;
        result.ApplyBinding(option);
      }
    }

    return result;
  }

  private Dictionary<Location, Dictionary<string, IdeImplementationView>> MigrateImplementationViews(DidChangeTextDocumentParams documentChange,
    Dictionary<Location, Dictionary<string, IdeImplementationView>> oldVerificationDiagnostics) {
    var result = new Dictionary<Location, Dictionary<string, IdeImplementationView>>();
    foreach (var entry in oldVerificationDiagnostics) {
      var newOuterRange = relocator.RelocateRange(entry.Key.Range, documentChange, CancellationToken.None);
      if (newOuterRange == null) {
        continue;
      }

      var newValue = new Dictionary<string, IdeImplementationView>();
      foreach (var innerEntry in entry.Value) {
        var newInnerRange = relocator.RelocateRange(innerEntry.Value.Range, documentChange, CancellationToken.None);
        if (newInnerRange != null) {
          newValue.Add(innerEntry.Key, new IdeImplementationView(Range: newInnerRange,
            Status: PublishedVerificationStatus.Stale,
            Diagnostics: relocator.RelocateDiagnostics(innerEntry.Value.Diagnostics, documentChange, CancellationToken.None)));
        }
      }
      result.Add(new Location() {
        Uri = entry.Key.Uri,
        Range = newOuterRange
      }, newValue);
    }
    return result;
  }

  public void Save(TextDocumentIdentifier documentId) {
    if (VerifyOnSave) {
      logger.LogDebug("Clearing result for workCompletedForCurrentVersion");
      _ = VerifyEverythingAsync(documentId.Uri.ToUri());
    }
  }

  /// <summary>
  /// Needs to be thread-safe
  /// </summary>
  /// <returns></returns>
  public bool CloseDocument(out Task close) {
    if (Interlocked.Decrement(ref openFileCount) == 0) {
      close = CloseAsync();
      return true;
    }

    close = Task.CompletedTask;
    return false;
  }

  public async Task CloseAsync() {
    CompilationManager.CancelPendingUpdates();
    try {
      await CompilationManager.LastDocument;
      observer.OnCompleted();
    } catch (OperationCanceledException) {
    }
  }

  public async Task<CompilationAfterParsing> GetLastDocumentAsync() {
    await workCompletedForCurrentVersion.WaitAsync();
    workCompletedForCurrentVersion.Release();
    return await CompilationManager.LastDocument;
  }

  public async Task<IdeState> GetSnapshotAfterParsingAsync() {
    try {
      var resolvedCompilation = await CompilationManager.ParsedCompilation;
      logger.LogDebug($"GetSnapshotAfterResolutionAsync, resolvedDocument.Version = {resolvedCompilation.Version}, " +
                      $"observer.LastPublishedState.Version = {observer.LastPublishedState.Compilation.Version}, threadId: {Thread.CurrentThread.ManagedThreadId}");
    } catch (OperationCanceledException) {
      logger.LogDebug("Caught OperationCanceledException in GetSnapshotAfterResolutionAsync");
    }

    return observer.LastPublishedState;
  }

  public async Task<IdeState> GetStateAfterResolutionAsync() {
    try {
      var resolvedCompilation = await CompilationManager.ResolvedCompilation;
      logger.LogDebug($"GetSnapshotAfterResolutionAsync, resolvedDocument.Version = {resolvedCompilation.Version}, " +
                      $"observer.LastPublishedState.Version = {observer.LastPublishedState.Compilation.Version}, threadId: {Thread.CurrentThread.ManagedThreadId}");
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

  // Test that when a project has multiple files, when saving/opening, only the affected Uri is verified when using OnSave.
  // Test that when a project has multiple files, everything is verified on opening one of them.
  public async Task VerifyEverythingAsync(Uri? uri) {
    _ = workCompletedForCurrentVersion.WaitAsync();
    try {
      var resolvedCompilation = await CompilationManager.ResolvedCompilation;

      var verifiables = resolvedCompilation.Verifiables.ToList();
      if (uri != null) {
        verifiables = verifiables.Where(d => d.Tok.Uri == uri).ToList();
      }

      // if (!verifiables.Any()) {
      //   CompilationManager.FinishedNotifications(resolvedCompilation);
      // }

      lock (RecentChanges) {
        var freshlyChangedVerifiables = GetChangedVerifiablesFromRanges(resolvedCompilation, RecentChanges);
        ChangedVerifiables = freshlyChangedVerifiables.Concat(ChangedVerifiables).Distinct()
          .Take(MaxRememberedChangedVerifiables).ToList();
        RecentChanges = new List<Location>();
      }

      int GetPriorityAttribute(ISymbol symbol) {
        return 0; // TODO lookup attribute
      }
      int TopToBottomPriority(ISymbol symbol) {
        return symbol.Tok.pos; // TODO lookup attribute as well
      }
      var implementationOrder = ChangedVerifiables.Select((v, i) => (v, i)).ToDictionary(k => k.v, k => k.i);
      var orderedVerifiables = verifiables.OrderBy(GetPriorityAttribute).CreateOrderedEnumerable(
        t => implementationOrder.GetOrDefault(t.Tok.GetFilePosition(), () => int.MaxValue),
        null, false).CreateOrderedEnumerable(TopToBottomPriority, null, false).ToList();

      foreach (var canVerify in orderedVerifiables) {
        // Wait for each task to try and run, so the order is respected.
        await CompilationManager.VerifyTask(resolvedCompilation, canVerify);
        // Needed to get gutter icon tests to pass reliably. Remove when we no longer have gutter icons on the server side.
        // The problem is that without this, the queueing of one task in Boogie interleaves with translating the next one.
        // Both of these actions can publish gutter icons, and they share a data store (the VerificationTree), so doing both updates before 
        // publishing can lead to less publications. 
        await Task.Delay(10);
      }

    }
    finally {
      logger.LogDebug("Setting result for workCompletedForCurrentVersion");
      workCompletedForCurrentVersion.Release();
    }
  }

  private IEnumerable<FilePosition> GetChangedVerifiablesFromRanges(CompilationAfterResolution translated, IEnumerable<Location> changedRanges) {
    IntervalTree<Position, Position> GetTree(Uri uri) {
      var intervalTree = new IntervalTree<Position, Position>();
      foreach (var canVerify in translated.Verifiables) {
        if (canVerify.Tok.Uri == uri) {
          intervalTree.Add(
            canVerify.RangeToken.StartToken.GetLspPosition(),
            canVerify.RangeToken.EndToken.GetLspPosition(true),
            canVerify.NameToken.GetLspPosition());
        }
      }
      return intervalTree;
    }

    Dictionary<Uri, IntervalTree<Position, Position>> trees = new();

    return changedRanges.SelectMany(changeRange => {
      var tree = trees.GetOrCreate(changeRange.Uri.ToUri(), () => GetTree(changeRange.Uri.ToUri()));
      return tree.Query(changeRange.Range.Start, changeRange.Range.End).Select(position => new FilePosition(changeRange.Uri.ToUri(), position));
    });
  }

  public void OpenDocument(Uri uri, bool triggerCompilation) {
    Interlocked.Increment(ref openFileCount);
    var lastPublishedState = observer.LastPublishedState;
    var migratedVerificationTrees = lastPublishedState.VerificationTrees;

    if (triggerCompilation) {
      StartNewCompilation(migratedVerificationTrees, lastPublishedState);
      TriggerVerificationForFile(uri);
    }
  }

  public void Dispose() {
    CompilationManager.CancelPendingUpdates();
  }
}
