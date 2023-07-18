using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive.Linq;
using System.Runtime.Caching;
using System.Threading;
using System.Threading.Tasks;
using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.FileSystemGlobbing;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public delegate ProjectManager CreateProjectManager(VersionedTextDocumentIdentifier documentIdentifier);

/// <summary>
/// Handles operation on a single document.
/// Handles migration of previously published document state
/// </summary>
public class ProjectManager {
  private readonly IRelocator relocator;

  private readonly IdeStateObserver observer;
  public CompilationManager CompilationManager { get; private set; }
  private IDisposable observerSubscription;
  private readonly ILogger<ProjectManager> logger;

  private bool VerifyOnOpen => serverOptions.Get(ServerCommand.Verification) == VerifyOnMode.Change;
  private bool VerifyOnChange => serverOptions.Get(ServerCommand.Verification) == VerifyOnMode.Change;
  private bool VerifyOnSave => serverOptions.Get(ServerCommand.Verification) == VerifyOnMode.Save;
  public List<Position> ChangedVerifiables { get; set; } = new();
  public List<Range> ChangedRanges { get; set; } = new();

  private readonly SemaphoreSlim workCompletedForCurrentVersion = new(0);
  private readonly DafnyOptions serverOptions;
  private readonly IFileSystem fileSystem;

  public ProjectManager(IFileSystem fileSystem,
    DafnyOptions serverOptions,
    ILogger<ProjectManager> logger,
    IRelocator relocator,
    CreateCompilationManager createCompilationManager,
    CreateIdeStateObserver createIdeStateObserver,
    VersionedTextDocumentIdentifier documentIdentifier) {
    this.fileSystem = fileSystem;
    this.serverOptions = serverOptions;
    this.createCompilationManager = createCompilationManager;
    this.relocator = relocator;
    this.logger = logger;

    observer = createIdeStateObserver(documentIdentifier);
    CompilationManager = createCompilationManager(
      DetermineDocumentOptions(serverOptions, documentIdentifier.Uri),
      documentIdentifier,
      null);

    observerSubscription = CompilationManager.DocumentUpdates.Select(d => d.InitialIdeState(serverOptions)).Subscribe(observer);

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
  public const int ProjectFileCacheExpiryTime = 100;

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

    var dafnyOptions = DetermineDocumentOptions(serverOptions, documentChange.TextDocument.Uri);
    CompilationManager = createCompilationManager(
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

  private DafnyOptions DetermineDocumentOptions(DafnyOptions serverOptions, DocumentUri uri) {
    DafnyProject? projectFile = GetProject(uri);

    var result = new DafnyOptions(serverOptions);
    result.Printer = new OutputLogger(logger);

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

  private DafnyProject GetProject(DocumentUri uri) {
    return FindProjectFile(uri.ToUri()) ?? ImplicitProject(uri);
  }

  public static DafnyProject ImplicitProject(DocumentUri uri) {
    var implicitProject = new DafnyProject {
      Includes = new[] { uri.GetFileSystemPath() },
      Uri = uri.ToUri(),
    };
    return implicitProject;
  }

  private DafnyProject? FindProjectFile(Uri uri) {

    DafnyProject? projectFile = null;

    var folder = Path.GetDirectoryName(uri.LocalPath);
    while (!string.IsNullOrEmpty(folder) && projectFile == null) {
      projectFile = GetProjectFile(uri, folder);
      folder = Path.GetDirectoryName(folder);
    }

    return projectFile;
  }

  private readonly MemoryCache projectFilePerFolderCache = new("projectFiles");
  private readonly object nullRepresentative = new(); // Needed because you can't store null in the MemoryCache, but that's a value we want to cache.
  private readonly CreateCompilationManager createCompilationManager;

  private DafnyProject? GetProjectFile(Uri sourceFile, string folderPath) {
    var cachedResult = projectFilePerFolderCache.Get(folderPath);
    if (cachedResult != null) {
      return cachedResult == nullRepresentative ? null : (DafnyProject?)cachedResult;
    }

    var result = GetProjectFileFromUriUncached(sourceFile, folderPath);
    projectFilePerFolderCache.Set(new CacheItem(folderPath, (object?)result ?? nullRepresentative), new CacheItemPolicy {
      AbsoluteExpiration = new DateTimeOffset(DateTime.Now.Add(TimeSpan.FromMilliseconds(ProjectFileCacheExpiryTime)))
    });
    return result;
  }

  private DafnyProject? GetProjectFileFromUriUncached(Uri sourceFile, string folderPath) {
    var configFileUri = new Uri(Path.Combine(folderPath, DafnyProject.FileName));
    if (!fileSystem.Exists(configFileUri)) {
      return null;
    }

    DafnyProject? projectFile = DafnyProject.Open(fileSystem, configFileUri, TextWriter.Null, TextWriter.Null);
    if (projectFile?.ContainsSourceFile(sourceFile) == false) {
      return null;
    }

    return projectFile;
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
    VerificationProgressReporter.UpdateTree(serverOptions, loaded, tree);
    var intervalTree = new IntervalTree<Position, Position>();
    foreach (var childTree in tree.Children) {
      intervalTree.Add(childTree.Range.Start, childTree.Range.End, childTree.Position);
    }

    return changedRanges.SelectMany(changeRange => intervalTree.Query(changeRange.Start, changeRange.End));
  }
}
