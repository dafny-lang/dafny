using System;
using System.Collections.Generic;
using System.IO;
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
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

/// <summary>
/// Handles operation on a single document.
/// Handles migration of previously published document state
/// </summary>
public class ProjectManager {
  private readonly IRelocator relocator;

  private readonly IServiceProvider services;
  private readonly IdeStateObserver observer;
  public CompilationManager CompilationManager { get; private set; }
  private IDisposable observerSubscription;
  private readonly ILogger<ProjectManager> logger;

  private bool VerifyOnOpen => options.Get(ServerCommand.Verification) == VerifyOnMode.Change;
  private bool VerifyOnChange => options.Get(ServerCommand.Verification) == VerifyOnMode.Change;
  private bool VerifyOnSave => options.Get(ServerCommand.Verification) == VerifyOnMode.Save;
  public List<Position> ChangedVerifiables { get; set; } = new();
  public List<Range> ChangedRanges { get; set; } = new();

  private readonly SemaphoreSlim workCompletedForCurrentVersion = new(0);
  private readonly DafnyOptions options;

  public ProjectManager(
    IServiceProvider services,
    VersionedTextDocumentIdentifier documentIdentifier) {
    this.services = services;
    options = services.GetRequiredService<DafnyOptions>();
    logger = services.GetRequiredService<ILogger<ProjectManager>>();
    relocator = services.GetRequiredService<IRelocator>();

    observer = new IdeStateObserver(services.GetRequiredService<ILogger<IdeStateObserver>>(),
      services.GetRequiredService<ITelemetryPublisher>(),
      services.GetRequiredService<INotificationPublisher>(),
      services.GetRequiredService<ITextDocumentLoader>(),
      documentIdentifier);
    CompilationManager = new CompilationManager(
      services,
      DetermineDocumentOptions(options, documentIdentifier.Uri),
      documentIdentifier,
      null);

    observerSubscription = CompilationManager.DocumentUpdates.Select(d => d.InitialIdeState(options)).Subscribe(observer);

    if (VerifyOnOpen) {
      var _ = VerifyEverythingAsync();
    } else {
      logger.LogDebug("Setting result for workCompletedForCurrentVersion");
      workCompletedForCurrentVersion.Release();
    }

    CompilationManager.Start();
  }

  private const int MaxRememberedChanges = 100;
  private const int MaxRememberedChangedVerifiables = 5;
  public void UpdateDocument(DidChangeTextDocumentParams documentChange) {

    logger.LogDebug("Clearing result for workCompletedForCurrentVersion");
    var _1 = workCompletedForCurrentVersion.WaitAsync();

    CompilationManager.CancelPendingUpdates();

    var lastPublishedState = observer.LastPublishedState;
    var migratedVerificationTree = lastPublishedState.VerificationTree == null ? null :
      relocator.RelocateVerificationTree(lastPublishedState.VerificationTree, documentChange, CancellationToken.None);
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

    var dafnyOptions = DetermineDocumentOptions(options, documentChange.TextDocument.Uri);
    CompilationManager = new CompilationManager(
      services,
      dafnyOptions,
      new VersionedTextDocumentIdentifier {
        Version = documentChange.TextDocument.Version!.Value,
        Uri = documentChange.TextDocument.Uri
      },
      // TODO do not pass this to CompilationManager but instead use it in FillMissingStateUsingLastPublishedDocument
      migratedVerificationTree
    );

    if (VerifyOnChange) {
      var _ = VerifyEverythingAsync();
    } else {
      logger.LogDebug("Setting result for workCompletedForCurrentVersion");
      workCompletedForCurrentVersion.Release();
    }

    observerSubscription.Dispose();
    var migratedUpdates = CompilationManager.DocumentUpdates.Select(document =>
      document.ToIdeState(lastPublishedState));
    observerSubscription = migratedUpdates.Subscribe(observer);
    logger.LogDebug($"Finished processing document update for version {documentChange.TextDocument.Version}");

    CompilationManager.Start();
  }

  private static DafnyOptions DetermineDocumentOptions(DafnyOptions serverOptions, DocumentUri uri) {
    DafnyProject? projectFile = null;

    var folder = Path.GetDirectoryName(uri.GetFileSystemPath());
    while (!string.IsNullOrEmpty(folder)) {
      var children = Directory.GetFiles(folder, "dfyconfig.toml");
      if (children.Length > 0) {
        projectFile = DafnyProject.Open(new Uri(children[0]), serverOptions.OutputWriter, serverOptions.ErrorWriter);
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

  private Dictionary<ImplementationId, IdeImplementationView> MigrateImplementationViews(DidChangeTextDocumentParams documentChange,
    IReadOnlyDictionary<ImplementationId, IdeImplementationView> oldVerificationDiagnostics) {
    var result = new Dictionary<ImplementationId, IdeImplementationView>();
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
      logger.LogDebug("Clearing result for workCompletedForCurrentVersion");
      var _1 = workCompletedForCurrentVersion.WaitAsync();
      var _2 = VerifyEverythingAsync();
    }
  }

  public async Task CloseAsync() {
    CompilationManager.CancelPendingUpdates();
    try {
      await CompilationManager.LastDocument;
    } catch (OperationCanceledException) {
    }
  }

  public async Task<CompilationAfterParsing> GetLastDocumentAsync() {
    await workCompletedForCurrentVersion.WaitAsync();
    workCompletedForCurrentVersion.Release();
    return await CompilationManager.LastDocument;
  }

  public async Task<IdeState> GetSnapshotAfterResolutionAsync() {
    try {
      var resolvedDocument = await CompilationManager.ResolvedDocument;
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
      var translatedDocument = await CompilationManager.TranslatedDocument;

      var implementationTasks = translatedDocument.VerificationTasks;

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
    var tree = new DocumentVerificationTree(loaded.Program, loaded.DocumentIdentifier);
    VerificationProgressReporter.UpdateTree(options, loaded, tree);
    var intervalTree = new IntervalTree<Position, Position>();
    foreach (var childTree in tree.Children) {
      intervalTree.Add(childTree.Range.Start, childTree.Range.End, childTree.Position);
    }

    return changedRanges.SelectMany(changeRange => intervalTree.Query(changeRange.Start, changeRange.End));
  }
}
