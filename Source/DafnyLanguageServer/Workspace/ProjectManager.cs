using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Reactive.Concurrency;
using System.Reactive.Disposables;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Reactive.Threading.Tasks;
using System.Threading;
using System.Threading.Tasks;
using IntervalTree;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Location = OmniSharp.Extensions.LanguageServer.Protocol.Models.Location;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public delegate ProjectManager CreateProjectManager(
  TaskScheduler scheduler,
  VerificationResultCache verificationCache,
  DafnyProject project);


/// <summary>
/// Handles operation on a single document.
/// Handles migration of previously published document state
/// </summary>
public class ProjectManager {

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

  public static readonly Option<bool> ReuseSolvers = new("--reuse-solvers",
    @"(experimental) Reuse solver for different verification of different document versions. Reduces verification latency but may reduce reliability of verification.".TrimStart()) {
    ArgumentHelpName = "event"
  };

  private readonly CreateMigrator createMigrator;
  public DafnyProject Project { get; }

  private readonly IdeStateObserver observer;
  public Compilation Compilation { get; private set; }
  private IDisposable observerSubscription;
  private readonly EventLoopScheduler ideStateUpdateScheduler = new();
  private readonly ILogger<ProjectManager> logger;

  private readonly VerificationResultCache cache;
  private readonly TaskScheduler scheduler;

  /// <summary>
  /// The version of this project.
  /// Is incremented when any file in the project is updated.
  /// Is used as part of project-wide notifications.
  /// Can be used by the client to ignore outdated notifications
  /// </summary>
  private int version;

  private ConcurrentDictionary<Uri, int> openFiles = new();

  private VerifyOnMode AutomaticVerificationMode => options.Get(Verification);

  private bool VerifyOnSave => options.Get(Verification) == VerifyOnMode.Save;
  public List<Location> RecentChanges { get; set; } = new();

  private readonly DafnyOptions options;
  private readonly DafnyOptions serverOptions;
  private readonly CreateCompilation createCompilation;
  private ExecutionEngine? boogieEngine;
  private readonly IFileSystem fileSystem;
  private readonly TelemetryPublisherBase telemetryPublisher;
  private readonly IProjectDatabase projectDatabase;
  private IdeState latestIdeState;
  private ReplaySubject<IdeState> states = new(1);
  public IObservable<IdeState> States => states;

  public ProjectManager(
    DafnyOptions serverOptions,
    ILogger<ProjectManager> logger,
    CreateMigrator createMigrator,
    IFileSystem fileSystem,
    TelemetryPublisherBase telemetryPublisher,
    IProjectDatabase projectDatabase,
    CreateCompilation createCompilation,
    CreateIdeStateObserver createIdeStateObserver,
    TaskScheduler scheduler,
    VerificationResultCache cache,
    DafnyProject project) {
    Project = project;
    this.telemetryPublisher = telemetryPublisher;
    this.projectDatabase = projectDatabase;
    this.serverOptions = serverOptions;
    this.fileSystem = fileSystem;
    this.createCompilation = createCompilation;
    this.createMigrator = createMigrator;
    this.logger = logger;

    options = DetermineProjectOptions(project, serverOptions);
    options.Printer = new OutputLogger(logger);
    this.cache = cache;
    this.scheduler = scheduler;
    var compilationInput = new CompilationInput(options, version, Project);
    var initialIdeState = IdeState.InitialIdeState(compilationInput);
    latestIdeState = initialIdeState;

    observer = createIdeStateObserver(initialIdeState);
    Compilation = this.createCompilation(GetBoogie(), compilationInput);

    observerSubscription = Disposable.Empty;
  }

  private const int MaxRememberedChanges = 100;

  public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
    StartNewCompilation(documentChange.TextDocument.Uri.ToUri(), documentChange);
  }

  private void StartNewCompilation(Uri triggeringFile, DidChangeTextDocumentParams? changes) {
    observerSubscription.Dispose();
    version += 1;

    var input = new CompilationInput(options, version, Project);
    IMigrator migrator = changes == null ? new NoopMigrator(triggeringFile) : createMigrator(changes, CancellationToken.None);
    // If we migrate the observer before accessing latestIdeState, we can be sure it's migrated before it receives new events.
    observer.Migrate(options, migrator, version);
    latestIdeState = latestIdeState.Migrate(options, migrator, version, false);

    Compilation.Dispose();
    Compilation = createCompilation(GetBoogie(), input);
    var migratedUpdates = GetStates(Compilation);
    states = new ReplaySubject<IdeState>(1);
    var statesSubscription = observerSubscription =
      migratedUpdates.Do(s => latestIdeState = s).Subscribe(states);

    var throttleTime = options.Get(UpdateThrottling);
    var throttledUpdates = throttleTime == 0 ? States : States.Sample(TimeSpan.FromMilliseconds(throttleTime));

    var throttledSubscription = throttledUpdates.Subscribe(observer);
    observerSubscription = new CompositeDisposable(statesSubscription, throttledSubscription);

    Compilation.Start();

    if (changes != null) {
      UpdateRecentChanges(changes, migrator);
    }
    TriggerVerificationForFile(triggeringFile);
  }

  private ExecutionEngine GetBoogie() {
    if (options.Get(ReuseSolvers)) {
      boogieEngine ??= new ExecutionEngine(options, cache, scheduler);
    } else {
      boogieEngine?.Dispose();
      boogieEngine = new ExecutionEngine(options, cache, scheduler);
    }
    return boogieEngine;
  }

  private void UpdateRecentChanges(DidChangeTextDocumentParams changes, IMigrator? migrator) {
    lock (RecentChanges) {
      var newChanges = changes.ContentChanges.Where(c => c.Range != null).
        Select(contentChange => new Location {
          Range = contentChange.Range!,
          Uri = changes.TextDocument.Uri
        });
      var migratedChanges = RecentChanges.Select(location => {
        if (location.Uri != changes.TextDocument.Uri) {
          return location;
        }

        var newRange = migrator!.MigrateRange(location.Range);
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
  }

  private IObservable<IdeState> GetStates(Compilation compilation) {
    var initialState = latestIdeState;
    var previousIdeState = initialState with {
      Input = compilation.Input,
    };

    return compilation.Updates.ObserveOn(ideStateUpdateScheduler).Select(ev => Update(ev));

    IdeState Update(ICompilationEvent ev) {
      if (ev is InternalCompilationException compilationException) {
        logger.LogError(compilationException.Exception, "error while handling document event");
        telemetryPublisher.PublishUnhandledException(compilationException.Exception);
      }

      try {
#pragma warning disable VSTHRD002
        previousIdeState = previousIdeState.UpdateState(options, logger, telemetryPublisher, projectDatabase, ev).Result;
#pragma warning restore VSTHRD002
        return previousIdeState;
      } catch (Exception e) {
        logger.LogError(e, "error while updating IDE state");
        telemetryPublisher.PublishUnhandledException(e);
        throw;
      }
    }
  }

  private void TriggerVerificationForFile(Uri triggeringFile) {
    if (AutomaticVerificationMode is VerifyOnMode.Change or VerifyOnMode.ChangeProject) {
      _ = VerifyEverythingAsync(AutomaticVerificationMode == VerifyOnMode.Change ? triggeringFile : null);
    } else {
      logger.LogDebug("Setting result for workCompletedForCurrentVersion");
    }
  }

  private static DafnyOptions DetermineProjectOptions(DafnyProject projectOptions, DafnyOptions serverOptions) {
    var result = new DafnyOptions(serverOptions);

    foreach (var option in LanguageServer.Options) {
      var hasProjectFileValue = projectOptions.TryGetValue(option, out var projectFileValue);
      if (hasProjectFileValue) {
        result.Options.OptionArguments[option] = projectFileValue;
        result.ApplyBinding(option);
      }
    }

    if (result.SolverIdentifier == "Z3") {
      result.SolverVersion = null;
    }

    result.DafnyProject = projectOptions;
    result.ApplyDefaultOptionsWithoutSettingsDefault();

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
  public bool CloseDocument(Uri uri) {
    if (openFiles.TryRemove(uri, out _) && openFiles.IsEmpty) {
      CloseAsync();
      return true;
    }

    return false;
  }

  public void CloseAsync() {
    Compilation.Dispose();
    try {
      observer.Clear();
    } catch (OperationCanceledException) {
    }
    Dispose();
  }

  public Task<IdeState> GetStateAfterParsingAsync() {
    return States.Where(s => s.Status > CompilationStatus.Parsing).FirstAsync().ToTask();
  }

  public Task<IdeState> GetStateAfterResolutionAsync() {
    return States.Where(s => s.Status is CompilationStatus.ParsingFailed or > CompilationStatus.ResolutionStarted).FirstAsync().ToTask();
  }

  /// <summary>
  /// This property and related code will be removed once we replace server gutter icons with client side computed gutter icons
  /// </summary>
  public static bool GutterIconTesting = false;

  public async Task VerifyEverythingAsync(Uri? uri) {
    var compilation = Compilation;
    var resolution = await compilation.Resolution;
    var canVerifies = resolution?.CanVerifies?.ToList();
    if (canVerifies == null) {
      return;
    }

    if (uri != null) {
      canVerifies = canVerifies.Where(d => d.Tok.Uri == uri).ToList();
    }

    List<FilePosition> changedVerifiables;
    lock (RecentChanges) {
      changedVerifiables = GetChangedVerifiablesFromRanges(canVerifies, RecentChanges).ToList();
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
    var orderedVerifiables = canVerifies
      .OrderByDescending(GetPriorityAttribute)
      .ThenBy(t => implementationOrder.GetOrDefault(t.Tok.GetFilePosition(), () => int.MaxValue))
      .ThenBy(TopToBottomPriority).ToList();
    logger.LogDebug($"Ordered verifiables: {string.Join(", ", orderedVerifiables.Select(v => v.NavigationToken.val))}");

    var orderedVerifiableLocations = orderedVerifiables.Select(v => v.NavigationToken.GetFilePosition()).ToList();
    if (GutterIconTesting) {
      foreach (var canVerify in orderedVerifiableLocations) {
        await compilation.VerifyLocation(canVerify, onlyPrepareVerificationForGutterTests: true);
      }

      logger.LogDebug($"Finished translation in VerifyEverything for {Project.Uri}");
    }

    foreach (var canVerify in orderedVerifiableLocations) {
      // Wait for each task to try and run, so the order is respected.
      await compilation.VerifyLocation(canVerify);
    }
  }

  private static IEnumerable<FilePosition> GetChangedVerifiablesFromRanges(IReadOnlyList<ICanVerify> verifiables, IEnumerable<Location> changedRanges) {
    IntervalTree<Position, Position> GetTree(Uri uri) {
      var intervalTree = new IntervalTree<Position, Position>();
      foreach (var canVerify in verifiables) {
        if (canVerify.Tok.Uri == uri) {
          intervalTree.Add(
            canVerify.Origin.StartToken.GetLspPosition(),
            canVerify.Origin.EndToken.GetLspPosition(true),
            canVerify.NavigationToken.GetLspPosition());
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
    openFiles.TryAdd(uri, 1);

    if (triggerCompilation) {
      StartNewCompilation(uri, null);
    }
  }

  public bool IsDisposed { get; private set; }

  public void Dispose() {
    IsDisposed = true;
    boogieEngine?.Dispose();
    Compilation.Dispose();
    observerSubscription.Dispose();
    // Dispose the update scheduler after the observer subscription, to prevent accessing a disposed object.
    ideStateUpdateScheduler.Dispose();
  }
}
