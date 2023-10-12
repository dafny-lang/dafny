using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Reactive;
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

public delegate ProjectManager CreateProjectManager(
  CustomStackSizePoolTaskScheduler scheduler,
  VerificationResultCache verificationCache,
  DafnyProject project);

public record FilePosition(Uri Uri, Position Position);

/// <summary>
/// Handles operation on a single document.
/// Handles migration of previously published document state
/// </summary>
public class ProjectManager : IDisposable {

  public const int DefaultThrottleTime = 100;
  public static readonly Option<int> UpdateThrottling = new("--update-throttling", () => DefaultThrottleTime,
    @"How many milliseconds the server will wait before sending new document updates to the client. Higher values reduce bandwidth at the cost of responsiveness".TrimStart()) {
    IsHidden = true
  };

  public static readonly Option<VerifyOnMode> Verification = new("--verify-on", () => VerifyOnMode.Change, @"
(experimental)
Determine when to automatically verify the program. Choose from: Never, OnChange (verify everything in a file when changing the file), OnChangeProject or OnSave.".TrimStart()) {
    ArgumentHelpName = "event"
  };

  private readonly CreateMigrator createMigrator;
  public DafnyProject Project { get; }

  private readonly IdeStateObserver observer;
  public CompilationManager CompilationManager { get; private set; }
  private IDisposable observerSubscription;
  private readonly INotificationPublisher notificationPublisher;
  private readonly IGutterIconAndHoverVerificationDetailsManager gutterIconManager;
  private readonly ILogger<ProjectManager> logger;

  /// <summary>
  /// The version of this project.
  /// Is incremented when any file in the project is updated.
  /// Is used as part of project-wide notifications.
  /// Can be used by the client to ignore outdated notifications
  /// </summary>
  private int version;

  private int openFileCount;

  private VerifyOnMode AutomaticVerificationMode => options.Get(Verification);

  private bool VerifyOnSave => options.Get(Verification) == VerifyOnMode.Save;
  public List<Location> RecentChanges { get; set; } = new();

  private readonly DafnyOptions options;
  private readonly DafnyOptions serverOptions;
  private readonly CreateCompilationManager createCompilationManager;
  private readonly ExecutionEngine boogieEngine;
  private readonly IFileSystem fileSystem;
  private Lazy<IdeState> latestIdeState;

  public ProjectManager(
    DafnyOptions serverOptions,
    ILogger<ProjectManager> logger,
    CreateMigrator createMigrator,
    IFileSystem fileSystem,
    INotificationPublisher notificationPublisher,
    IGutterIconAndHoverVerificationDetailsManager gutterIconManager,
    CreateCompilationManager createCompilationManager,
    CreateIdeStateObserver createIdeStateObserver,
    CustomStackSizePoolTaskScheduler scheduler,
    VerificationResultCache cache,
    DafnyProject project) {
    Project = project;
    this.gutterIconManager = gutterIconManager;
    this.notificationPublisher = notificationPublisher;
    this.serverOptions = serverOptions;
    this.fileSystem = fileSystem;
    this.createCompilationManager = createCompilationManager;
    this.createMigrator = createMigrator;
    this.logger = logger;

    options = DetermineProjectOptions(project, serverOptions);
    options.Printer = new OutputLogger(logger);
    this.boogieEngine = new ExecutionEngine(options, cache, scheduler);
    var initialCompilation = CreateInitialCompilation();
    var initialIdeState = initialCompilation.InitialIdeState(initialCompilation, options);
    latestIdeState = new Lazy<IdeState>(initialIdeState);

    observer = createIdeStateObserver(initialIdeState);
    CompilationManager = createCompilationManager(
        options, boogieEngine, initialCompilation, ImmutableDictionary<Uri, DocumentVerificationTree>.Empty
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
    var migrator = createMigrator(documentChange, CancellationToken.None);
    Lazy<IdeState> lazyPreviousCompilationLastIdeState = latestIdeState;
    var upcomingVersion = version + 1;
    latestIdeState = new Lazy<IdeState>(() => {
      // If we migrate the observer before accessing latestIdeState, we can be sure it's migrated before it receives new events.
      observer.Migrate(migrator, upcomingVersion);
      return lazyPreviousCompilationLastIdeState.Value.Migrate(migrator, upcomingVersion);
    });
    StartNewCompilation();

    lock (RecentChanges) {
      var newChanges = documentChange.ContentChanges.Where(c => c.Range != null).
        Select(contentChange => new Location {
          Range = contentChange.Range!,
          Uri = documentChange.TextDocument.Uri
        });
      var migratedChanges = RecentChanges.Select(location => {
        if (location.Uri != documentChange.TextDocument.Uri) {
          return location;
        }

        var newRange = migrator.MigrateRange(location.Range);
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
    TriggerVerificationForFile(documentChange.TextDocument.Uri.ToUri());
  }

  private void StartNewCompilation() {
    var compilationVersion = ++version;
    logger.LogDebug("Clearing result for workCompletedForCurrentVersion");

    Lazy<IdeState> migratedLazyPreviousCompilationLastIdeState = latestIdeState;
    observerSubscription.Dispose();

    CompilationManager.Dispose();
    CompilationManager = createCompilationManager(
      options,
      boogieEngine,
      CreateInitialCompilation(),
      latestIdeState.Value.VerificationTrees);

    var migratedUpdates = CompilationManager.CompilationUpdates.Select(document => {
      if (document.Version == compilationVersion) {
        latestIdeState =
          new Lazy<IdeState>(() => document.ToIdeState(migratedLazyPreviousCompilationLastIdeState.Value));
      }

      return latestIdeState;
    });
    var throttleTime = options.Get(UpdateThrottling);
    var throttledUpdates = throttleTime == 0 ? migratedUpdates : migratedUpdates.Sample(TimeSpan.FromMilliseconds(throttleTime));
    observerSubscription = throttledUpdates.
      Select(x => x.Value).Subscribe(observer);

    CompilationManager.Start();
  }

  private void TriggerVerificationForFile(Uri triggeringFile) {
    if (AutomaticVerificationMode is VerifyOnMode.Change or VerifyOnMode.ChangeProject) {
      var _ = VerifyEverythingAsync(AutomaticVerificationMode == VerifyOnMode.Change ? triggeringFile : null);
    } else {
      logger.LogDebug("Setting result for workCompletedForCurrentVersion");
    }
  }

  private static DafnyOptions DetermineProjectOptions(DafnyProject projectOptions, DafnyOptions serverOptions) {
    var result = new DafnyOptions(serverOptions);

    foreach (var option in LanguageServer.Options) {
      var hasProjectFileValue = projectOptions.TryGetValue(option, TextWriter.Null, out var projectFileValue);
      if (hasProjectFileValue) {
        result.Options.OptionArguments[option] = projectFileValue;
        result.ApplyBinding(option);
      }
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
    Dispose();
  }

  public async Task<CompilationAfterParsing> GetLastDocumentAsync() {
    logger.LogDebug($"GetLastDocumentAsync passed ProjectManager check for {Project.Uri}");
    return await CompilationManager.LastDocument;
  }

  public async Task<IdeState> GetStateAfterParsingAsync() {
    try {
      var parsedCompilation = await CompilationManager.ParsedCompilation;
      logger.LogDebug($"GetSnapshotAfterParsingAsync returns compilation version {parsedCompilation.Version}");
    } catch (OperationCanceledException) {
      logger.LogDebug($"GetSnapshotAfterResolutionAsync caught OperationCanceledException for parsed compilation {Project.Uri}");
    }

    logger.LogDebug($"GetSnapshotAfterParsingAsync returns state version {latestIdeState.Value.Version}");
    return latestIdeState.Value;
  }

  public async Task<IdeState> GetStateAfterResolutionAsync() {
    try {
      var resolvedCompilation = await CompilationManager.ResolvedCompilation;
      logger.LogDebug($"GetStateAfterResolutionAsync returns compilation version {resolvedCompilation.Version}");
      logger.LogDebug($"GetStateAfterResolutionAsync returns state version {latestIdeState.Value.Version}");
      return latestIdeState.Value;
    } catch (OperationCanceledException) {
      logger.LogDebug($"GetSnapshotAfterResolutionAsync caught OperationCanceledException for resolved compilation {Project.Uri}");
      throw;
    }

  }

  public async Task<IdeState> GetIdeStateAfterVerificationAsync() {
    try {
      await GetLastDocumentAsync();
    } catch (OperationCanceledException) {
    }

    return latestIdeState.Value;
  }


  /// <summary>
  /// This property and related code will be removed once we replace server gutter icons with client side computed gutter icons
  /// </summary>
  public static bool GutterIconTesting = false;

  public async Task VerifyEverythingAsync(Uri? uri) {
    var compilationManager = CompilationManager;
    try {
      compilationManager.IncrementJobs();
      var resolvedCompilation = await compilationManager.ResolvedCompilation;

      var verifiables = resolvedCompilation.Verifiables?.ToList();
      if (verifiables == null) {
        return;
      }

      if (uri != null) {
        verifiables = verifiables.Where(d => d.Tok.Uri == uri).ToList();
      }

      List<FilePosition> changedVerifiables;
      lock (RecentChanges) {
        changedVerifiables = GetChangedVerifiablesFromRanges(verifiables, RecentChanges).ToList();
      }

      int GetPriorityAttribute(ISymbol symbol) {
        if (symbol is IAttributeBearingDeclaration hasAttributes &&
            hasAttributes.HasUserAttribute("priority", out var attribute) &&
            attribute.Args.Count >= 1 && attribute.Args[0] is LiteralExpr { Value: BigInteger priority }) {
          return (int)priority;
        }
        return 0;
      }

      int TopToBottomPriority(ISymbol symbol) {
        return symbol.Tok.pos;
      }
      var implementationOrder = changedVerifiables.Select((v, i) => (v, i)).ToDictionary(k => k.v, k => k.i);
      var orderedVerifiables = verifiables.OrderByDescending(GetPriorityAttribute).CreateOrderedEnumerable(
        t => implementationOrder.GetOrDefault(t.Tok.GetFilePosition(), () => int.MaxValue),
        null, false).CreateOrderedEnumerable(TopToBottomPriority, null, false).ToList();
      logger.LogDebug($"Ordered verifiables: {string.Join(", ", orderedVerifiables.Select(v => v.NameToken.val))}");

      var orderedVerifiableLocations = orderedVerifiables.Select(v => v.NameToken.GetFilePosition()).ToList();
      if (GutterIconTesting) {
        foreach (var canVerify in orderedVerifiableLocations) {
          await compilationManager.VerifySymbol(canVerify, true);
        }

        logger.LogDebug($"Finished translation in VerifyEverything for {Project.Uri}");
      }

      foreach (var canVerify in orderedVerifiableLocations) {
        // Wait for each task to try and run, so the order is respected.
        await compilationManager.VerifySymbol(canVerify);
      }
    }
    finally {
      logger.LogDebug("Setting result for workCompletedForCurrentVersion");
      compilationManager.DecrementJobs();
    }
  }

  private IEnumerable<FilePosition> GetChangedVerifiablesFromRanges(IReadOnlyList<ICanVerify> verifiables, IEnumerable<Location> changedRanges) {
    IntervalTree<Position, Position> GetTree(Uri uri) {
      var intervalTree = new IntervalTree<Position, Position>();
      foreach (var canVerify in verifiables) {
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
      var uri = changeRange.Uri.ToUri();
      var tree = trees.GetOrCreate(uri, () => GetTree(uri));
      return tree.Query(changeRange.Range.Start, changeRange.Range.End).Select(position => new FilePosition(uri, position));
    }).Distinct();
  }

  public void OpenDocument(Uri uri, bool triggerCompilation) {
    Interlocked.Increment(ref openFileCount);

    if (triggerCompilation) {
      StartNewCompilation();
      TriggerVerificationForFile(uri);
    }
  }

  public void Dispose() {
    boogieEngine.Dispose();
    observerSubscription.Dispose();
    CompilationManager.Dispose();
  }
}
