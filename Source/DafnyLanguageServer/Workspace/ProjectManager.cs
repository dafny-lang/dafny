using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive.Linq;
using System.Threading;
using System.Threading.Tasks;
using IntervalTree;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class ProjectManager : IDisposable {
  private readonly IRelocator relocator;

  private readonly IServiceProvider services;
  public DafnyProject Project { get; }
  private readonly IdeStateObserver observer;
  public CompilationManager? CompilationManager { get; private set; }
  private IDisposable? observerSubscription;
  private readonly ILogger<ProjectManager> logger;
  private ExecutionEngine boogieEngine;
  private int version = 1;

  private bool VerifyOnOpenChange => options.Get(ServerCommand.Verification) == VerifyOnMode.Change;
  private bool VerifyOnSave => options.Get(ServerCommand.Verification) == VerifyOnMode.Save;
  public List<Position> ChangedVerifiables { get; set; } = new();
  public List<Range> ChangedRanges { get; set; } = new();

  private readonly SemaphoreSlim workCompletedForCurrentVersion = new(0);
  private readonly DafnyOptions options;
  private readonly IFileSystem fileSystem;
  private DafnyOptions serverOptions;

  public ProjectManager(IServiceProvider services, VerificationResultCache verificationCache, DafnyProject project) {
    this.services = services;
    Project = project;
    serverOptions = services.GetRequiredService<DafnyOptions>();
    logger = services.GetRequiredService<ILogger<ProjectManager>>();
    relocator = services.GetRequiredService<IRelocator>();
    fileSystem = services.GetRequiredService<IFileSystem>();

    // Moet CliRootSourceUris uit options??? Of moet er een extra veld zijn, 
    options = DetermineProjectOptions(project, serverOptions);
    observer = new IdeStateObserver(services.GetRequiredService<ILogger<IdeStateObserver>>(),
      services.GetRequiredService<ITelemetryPublisher>(),
      services.GetRequiredService<INotificationPublisher>(),
      services.GetRequiredService<ITextDocumentLoader>(),
      project);
    boogieEngine = new ExecutionEngine(options, verificationCache);
    options.Printer = new OutputLogger(logger);

    // Remove this next part???
    // var compilationStart = new Compilation(version, Project);
    // CompilationManager = new CompilationManager(
    //   services,
    //   options,
    //   boogieEngine, compilationStart, null);
    //
    // observerSubscription = CompilationManager.CompilationUpdates.Select(d =>
    //   d.InitialIdeState(compilationStart, options)).Subscribe(observer);
    //
    // CompilationManager.Start();
  }

  private const int MaxRememberedChanges = 100;
  private const int MaxRememberedChangedVerifiables = 5;

  // TODO test that migration doesn't affect the wrong document.
  // Also test that changed ranges is computed for the right document.
  public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
    CompilationManager?.CancelPendingUpdates();

    var lastPublishedState = observer.LastPublishedState;
    var migratedVerificationTree = lastPublishedState.VerificationTree == null ? null
      : relocator.RelocateVerificationTree(lastPublishedState.VerificationTree, documentChange, CancellationToken.None);
    lastPublishedState = lastPublishedState with {
      ImplementationIdToView = MigrateImplementationViews(documentChange, lastPublishedState.ImplementationIdToView),
      SignatureAndCompletionTable = relocator.RelocateSymbols(lastPublishedState.SignatureAndCompletionTable, documentChange, CancellationToken.None),
      VerificationTree = migratedVerificationTree
    };

    lock (ChangedRanges) {
      ChangedRanges = documentChange.ContentChanges.Select(contentChange => contentChange.Range).Concat(
        ChangedRanges.Select(range =>
            relocator.RelocateRange(range, documentChange, CancellationToken.None))).
          Where(r => r != null).Take(MaxRememberedChanges).ToList()!;
    }

    StartNewCompilation(documentChange.TextDocument.Uri.ToUri(), migratedVerificationTree, lastPublishedState);
  }

  private void StartNewCompilation(Uri triggeringFile, VerificationTree? migratedVerificationTree,
    IdeState lastPublishedState) {
    version++;
    logger.LogDebug("Clearing result for workCompletedForCurrentVersion");
    var _1 = workCompletedForCurrentVersion.WaitAsync();

    CompilationManager = new CompilationManager(
      services,
      options,
      boogieEngine,
      new Compilation(version, Project),
      // TODO do not pass this to CompilationManager but instead use it in FillMissingStateUsingLastPublishedDocument
      migratedVerificationTree
    );

    if (VerifyOnOpenChange) {
      var _ = VerifyEverythingAsync(triggeringFile);
    } else {
      logger.LogDebug("Setting result for workCompletedForCurrentVersion");
      workCompletedForCurrentVersion.Release();
    }

    observerSubscription?.Dispose();
    var migratedUpdates = CompilationManager.CompilationUpdates.Select(document =>
      document.ToIdeState(lastPublishedState));
    observerSubscription = migratedUpdates.Subscribe(observer);

    CompilationManager.Start();
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

  private Dictionary<ImplementationId, IdeImplementationView> MigrateImplementationViews(DidChangeTextDocumentParams documentChange,
    IReadOnlyDictionary<ImplementationId, IdeImplementationView> oldVerificationDiagnostics) {
    var result = new Dictionary<ImplementationId, IdeImplementationView>();
    foreach (var entry in oldVerificationDiagnostics) {
      var newRange = relocator.RelocateRange(entry.Value.Range, documentChange, CancellationToken.None);
      if (newRange != null) {
        result.Add(entry.Key with {
          Position = relocator.RelocatePosition(entry.Key.Position, documentChange, CancellationToken.None)
        }, entry.Value with {
          Range = newRange,
          Diagnostics = relocator.RelocateDiagnostics(entry.Value.Diagnostics, documentChange, CancellationToken.None)
        });
      }
    }
    return result;
  }

  public void Save(TextDocumentIdentifier documentId) {
    if (VerifyOnSave) {
      logger.LogDebug("Clearing result for workCompletedForCurrentVersion");
      var _1 = workCompletedForCurrentVersion.WaitAsync();
      var _2 = VerifyEverythingAsync(documentId.Uri.ToUri());
    }
  }

  public async Task CloseAsync() {
    if (CompilationManager == null) {
      return;
    }
    CompilationManager.CancelPendingUpdates();
    try {
      await CompilationManager.LastDocument;
      observer.OnCompleted();
    } catch (TaskCanceledException) {
    }
  }

  public async Task<CompilationAfterParsing> GetLastDocumentAsync() {
    await workCompletedForCurrentVersion.WaitAsync();
    workCompletedForCurrentVersion.Release();
    return await CompilationManager.LastDocument;
  }

  public async Task<IdeState> GetSnapshotAfterResolutionAsync() {
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
  private async Task VerifyEverythingAsync(Uri uri) {
    try {
      var translatedDocument = await CompilationManager.TranslatedCompilation;

      var implementationTasks = translatedDocument.VerificationTasks.
        Where(d => ((IToken)d.Implementation.tok).Uri == uri).ToList();

      if (!implementationTasks.Any()) {
        CompilationManager.FinishedNotifications(translatedDocument);
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
        CompilationManager.VerifyTask(translatedDocument, implementationTask);
      }
    }
    finally {
      logger.LogDebug("Setting result for workCompletedForCurrentVersion");
      workCompletedForCurrentVersion.Release();
    }
  }

  private IEnumerable<Position> GetChangedVerifiablesFromRanges(CompilationAfterResolution loaded, IEnumerable<Range> changedRanges) {
    var tree = new DocumentVerificationTree(loaded.Program, loaded.Project.Uri);
    VerificationProgressReporter.UpdateTree(options, loaded, tree);
    var intervalTree = new IntervalTree<Position, Position>();
    foreach (var childTree in tree.Children) {
      intervalTree.Add(childTree.Range.Start, childTree.Range.End, childTree.Position);
    }

    return changedRanges.SelectMany(changeRange => intervalTree.Query(changeRange.Start, changeRange.End));
  }

  public void OpenDocument(TextDocumentItem document) {
    CompilationManager?.CancelPendingUpdates();

    var lastPublishedState = observer.LastPublishedState;
    var migratedVerificationTree = lastPublishedState.VerificationTree;

    StartNewCompilation(document.Uri.ToUri(), migratedVerificationTree, lastPublishedState);
  }

  public void Dispose() {
    boogieEngine.Dispose();
  }
}
