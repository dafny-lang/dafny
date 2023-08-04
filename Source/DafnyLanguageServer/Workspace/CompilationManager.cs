using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Concurrency;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using VC;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public delegate CompilationManager CreateCompilationManager(
  DafnyOptions options,
  ExecutionEngine boogieEngine,
  Compilation compilation,
  VerificationTree? migratedVerificationTree);

/// <summary>
/// The compilation of a single document version.
/// The document will be parsed, resolved, translated to Boogie and verified.
///
/// Compilation may be configured to pause after translation,
/// requiring a call to CompilationManager.Verify for the document to be verified.
///
/// Compilation is agnostic to document updates, it does not handle the migration of old document state.
/// </summary>
public class CompilationManager {

  private readonly ILogger logger;
  private readonly ITextDocumentLoader documentLoader;
  private readonly ICompilationStatusNotificationPublisher statusPublisher;
  private readonly INotificationPublisher notificationPublisher;
  private readonly IProgramVerifier verifier;
  private readonly IVerificationProgressReporter verificationProgressReporter;

  // TODO CompilationManager shouldn't be aware of migration
  private readonly VerificationTree? migratedVerificationTree;

  private TaskCompletionSource started = new();
  private readonly IScheduler verificationUpdateScheduler = new EventLoopScheduler();
  private readonly CancellationTokenSource cancellationSource;

  private TaskCompletionSource verificationCompleted = new();
  private readonly DafnyOptions options;
  private readonly Compilation startingCompilation;
  private readonly ExecutionEngine boogieEngine;

  private readonly Subject<Compilation> compilationUpdates = new();
  public IObservable<Compilation> CompilationUpdates => compilationUpdates;

  public Task<CompilationAfterParsing> ResolvedCompilation { get; }
  public Task<CompilationAfterTranslation> TranslatedCompilation { get; }

  public CompilationManager(
    ILogger<CompilationManager> logger,
    ITextDocumentLoader documentLoader,
    INotificationPublisher notificationPublisher,
    IProgramVerifier verifier,
    ICompilationStatusNotificationPublisher statusPublisher,
    IVerificationProgressReporter verificationProgressReporter,
    DafnyOptions options,
    ExecutionEngine boogieEngine,
    Compilation compilation,
    VerificationTree? migratedVerificationTree
    ) {
    this.options = options;
    startingCompilation = compilation;
    this.boogieEngine = boogieEngine;
    this.migratedVerificationTree = migratedVerificationTree;

    this.documentLoader = documentLoader;
    this.logger = logger;
    this.notificationPublisher = notificationPublisher;
    this.verifier = verifier;
    this.statusPublisher = statusPublisher;
    this.verificationProgressReporter = verificationProgressReporter;
    cancellationSource = new();
    cancellationSource.Token.Register(() => started.TrySetCanceled(cancellationSource.Token));

    MarkVerificationFinished();

    ResolvedCompilation = ResolveAsync();
    TranslatedCompilation = TranslateAsync();
  }

  public void Start() {
    started.TrySetResult();
  }

  private async Task<CompilationAfterParsing> ResolveAsync() {
    try {
      await started.Task;
      var documentAfterParsing = await documentLoader.LoadAsync(options, startingCompilation, cancellationSource.Token);

      // TODO, let gutter icon publications also used the published CompilationView.
      var state = documentAfterParsing.InitialIdeState(startingCompilation, options);
      state = state with {
        VerificationTree = migratedVerificationTree ?? state.VerificationTree
      };
      notificationPublisher.PublishGutterIcons(state, false);

      logger.LogDebug($"documentUpdates.HasObservers: {compilationUpdates.HasObservers}, threadId: {Thread.CurrentThread.ManagedThreadId}");
      compilationUpdates.OnNext(documentAfterParsing);
      logger.LogDebug($"Passed documentAfterParsing to documentUpdates.OnNext, resolving ResolvedDocument task for version {documentAfterParsing.Version}.");
      return documentAfterParsing;

    } catch (Exception e) {
      compilationUpdates.OnError(e);
      throw;
    }
  }

  private async Task<CompilationAfterTranslation> TranslateAsync() {
    var parsedCompilation = await ResolvedCompilation;
    if (!options.Verify) {
      throw new OperationCanceledException();
    }
    if (parsedCompilation is not CompilationAfterResolution resolvedCompilation) {
      throw new OperationCanceledException();
    }

    try {
      var translatedDocument = await PrepareVerificationTasksAsync(resolvedCompilation, cancellationSource.Token);
      compilationUpdates.OnNext(translatedDocument);
      foreach (var task in translatedDocument.VerificationTasks!) {
        cancellationSource.Token.Register(task.Cancel);
      }

      return translatedDocument;
    } catch (Exception e) {
      compilationUpdates.OnError(e);
      throw;
    }
  }

  public async Task<CompilationAfterTranslation> PrepareVerificationTasksAsync(
    CompilationAfterResolution loaded,
    CancellationToken cancellationToken) {
    if (loaded.ResolutionDiagnostics.Values.SelectMany(x => x).Any(d =>
          d.Level == ErrorLevel.Error &&
          d.Source != MessageSource.Compiler &&
          d.Source != MessageSource.Verifier)) {
      throw new TaskCanceledException();
    }

    var _ = statusPublisher.SendStatusNotification(loaded, CompilationStatus.PreparingVerification);

    var verificationTasks =
      await verifier.GetVerificationTasksAsync(boogieEngine, loaded, cancellationToken);

    var initialViews = new Dictionary<ImplementationId, ImplementationView>();
    foreach (var task in verificationTasks) {
      var status = StatusFromBoogieStatus(task.CacheStatus);
      var implementationId = GetImplementationId(task.Implementation);
      try {
        if (task.CacheStatus is Completed completed) {
          var view = new ImplementationView(task.Implementation.tok.GetLspRange(true), status,
            GetDiagnosticsFromResult(loaded, completed.Result).ToList());
          initialViews.Add(implementationId, view);
        } else {
          var view = new ImplementationView(task.Implementation.tok.GetLspRange(true), status, Array.Empty<DafnyDiagnostic>());
          initialViews.Add(implementationId, view);
        }
      } catch (ArgumentException) {
        logger.LogCritical($"Two different implementation tasks have the same id, second name is {task.Implementation.Name}.");
      }
    }

    var translated = new CompilationAfterTranslation(
      loaded,
      loaded.ResolutionDiagnostics, verificationTasks,
      new(),
      initialViews,
      migratedVerificationTree ?? (loaded.Project.IsImplicitProject ? new DocumentVerificationTree(loaded.Program, loaded.Project.Uri) : null)
      );

    verificationProgressReporter.RecomputeVerificationTree(translated);

    if (ReportGutterStatus) {
      verificationProgressReporter.ReportRealtimeDiagnostics(translated, false);
    }
    verificationProgressReporter.ReportImplementationsBeforeVerification(translated,
      verificationTasks.Select(t => t.Implementation).ToArray());
    return translated;
  }

  private static ImplementationId GetImplementationId(Implementation implementation) {
    var prefix = implementation.Name.Split(Translator.NameSeparator)[0];

    // Refining declarations get the token of what they're refining, so to distinguish them we need to
    // add the refining module name to the prefix.
    if (implementation.tok is RefinementToken refinementToken) {
      prefix += "." + refinementToken.InheritingModule.Name;
    }
    return new ImplementationId(((IToken)implementation.tok).Uri, implementation.tok.GetLspPosition(), prefix);
  }

  private void SetAllUnvisitedMethodsAsVerified(CompilationAfterTranslation compilation) {
    verificationProgressReporter.SetAllUnvisitedMethodsAsVerified(compilation);
  }

  private int runningVerificationJobs = 0;
  public bool VerifyTask(CompilationAfterTranslation compilation, IImplementationTask implementationTask) {

    var statusUpdates = implementationTask.TryRun();
    if (statusUpdates == null) {
      if (implementationTask.CacheStatus is Completed completedCache) {
        foreach (var result in completedCache.Result.VCResults) {
          verificationProgressReporter.ReportVerifyImplementationRunning(compilation, implementationTask.Implementation);
          verificationProgressReporter.ReportAssertionBatchResult(compilation,
            new AssertionBatchResult(implementationTask.Implementation, result));
        }
        verificationProgressReporter.ReportEndVerifyImplementation(compilation, implementationTask.Implementation,
          completedCache.Result);
      }

      return false;
    }

    Interlocked.Increment(ref runningVerificationJobs);
    MarkVerificationStarted();
    statusUpdates.ObserveOn(verificationUpdateScheduler).Subscribe(
      update => {
        try {
          HandleStatusUpdate(compilation, implementationTask, update);
        } catch (Exception e) {
          logger.LogCritical(e, "Caught exception in statusUpdates OnNext.");
        }
      },
      e => {
        logger.LogError(e, "Caught error in statusUpdates observable.");
        StatusUpdateHandlerFinally();
      },
      StatusUpdateHandlerFinally
    );

    void StatusUpdateHandlerFinally() {
      try {
        var remainingJobs = Interlocked.Decrement(ref runningVerificationJobs);
        if (remainingJobs == 0) {
          logger.LogDebug($"Calling FinishedNotifications because there are no remaining verification jobs for version {compilation.Version}.");
          FinishedNotifications(compilation);
        }
      } catch (Exception e) {
        logger.LogCritical(e, "Caught exception while handling finally code of statusUpdates handler.");
      }
    }

    return true;
  }

  public void FinishedNotifications(CompilationAfterTranslation compilation) {
    MarkVerificationFinished();
    if (ReportGutterStatus) {
      // All unvisited trees need to set them as "verified"
      if (!cancellationSource.IsCancellationRequested) {
        SetAllUnvisitedMethodsAsVerified(compilation);
      }

      verificationProgressReporter.ReportRealtimeDiagnostics(compilation, true);
    }
  }

  private void HandleStatusUpdate(CompilationAfterTranslation compilation, IImplementationTask implementationTask, IVerificationStatus boogieStatus) {
    var id = GetImplementationId(implementationTask.Implementation);
    var status = StatusFromBoogieStatus(boogieStatus);
    var implementationRange = implementationTask.Implementation.tok.GetLspRange(true);
    logger.LogDebug($"Received status {boogieStatus} for {implementationTask.Implementation.Name}, version {compilation.Counterexamples}");
    if (boogieStatus is Running) {
      verificationProgressReporter.ReportVerifyImplementationRunning(compilation, implementationTask.Implementation);
    }

    if (boogieStatus is BatchCompleted batchCompleted) {
      logger.LogDebug($"Received batch completed for {implementationTask.Implementation.tok}");
      verificationProgressReporter.ReportAssertionBatchResult(compilation,
        new AssertionBatchResult(implementationTask.Implementation, batchCompleted.VcResult));
    }

    if (boogieStatus is Completed completed) {
      logger.LogDebug($"Received verification task completed for {implementationTask.Implementation.tok}, version {compilation.Counterexamples}");
      var verificationResult = completed.Result;
      foreach (var counterExample in verificationResult.Errors) {
        compilation.Counterexamples.Add(counterExample);
      }
      // Sometimes, the boogie status is set as Completed
      // but the assertion batches were not reported yet.
      // because they are on a different thread.
      // This loop will ensure that every vc result has been dealt with
      // before we report that the verification of the implementation is finished 
      foreach (var result in completed.Result.VCResults) {
        logger.LogDebug($"Possibly duplicate reporting assertion batch {result.vcNum} as completed in {implementationTask.Implementation.tok}, version {compilation.Counterexamples}");
        verificationProgressReporter.ReportAssertionBatchResult(compilation,
          new AssertionBatchResult(implementationTask.Implementation, result));
      }

      var diagnostics = GetDiagnosticsFromResult(compilation, verificationResult).ToList();
      var view = new ImplementationView(implementationRange, status, diagnostics);
      compilation.ImplementationIdToView[id] = view;
      verificationProgressReporter.ReportEndVerifyImplementation(compilation, implementationTask.Implementation, verificationResult);
    } else {
      var existingView = compilation.ImplementationIdToView.GetValueOrDefault(id) ??
                         new ImplementationView(implementationRange, status, Array.Empty<DafnyDiagnostic>());
      compilation.ImplementationIdToView[id] = existingView with { Status = status };
    }

    compilationUpdates.OnNext(compilation);
  }

  private bool ReportGutterStatus => options.Get(ServerCommand.LineVerificationStatus);

  private List<DafnyDiagnostic> GetDiagnosticsFromResult(CompilationAfterResolution compilation, VerificationResult result) {
    var errorReporter = new DiagnosticErrorReporter(options, compilation.Uri.ToUri());
    foreach (var counterExample in result.Errors) {
      errorReporter.ReportBoogieError(counterExample.CreateErrorInformation(result.Outcome, options.ForceBplErrors));
    }

    var outcomeError = result.GetOutcomeError(options);
    if (outcomeError != null) {
      errorReporter.ReportBoogieError(outcomeError);
    }

    var diagnostics = errorReporter.AllDiagnosticsCopy.Values.SelectMany(x => x);
    return diagnostics.OrderBy(d => d.Token.GetLspPosition()).ToList();
  }

  private static PublishedVerificationStatus StatusFromBoogieStatus(IVerificationStatus verificationStatus) {
    switch (verificationStatus) {
      case Stale:
        return PublishedVerificationStatus.Stale;
      case Queued:
        return PublishedVerificationStatus.Queued;
      case Running:
        return PublishedVerificationStatus.Running;
      case Completed completed:
        return completed.Result.Outcome == ConditionGeneration.Outcome.Correct
          ? PublishedVerificationStatus.Correct
          : PublishedVerificationStatus.Error;
      case BatchCompleted batchCompleted:
        return batchCompleted.VcResult.outcome == ProverInterface.Outcome.Valid
          ? PublishedVerificationStatus.Correct
          : PublishedVerificationStatus.Error;
      default:
        throw new ArgumentOutOfRangeException();
    }
  }

  public void CancelPendingUpdates() {
    cancellationSource.Cancel();
  }

  public void MarkVerificationStarted() {
    logger.LogTrace("MarkVerificationStarted called");
    if (verificationCompleted.Task.IsCompleted) {
      verificationCompleted = new TaskCompletionSource();
    }
  }

  public void MarkVerificationFinished() {
    logger.LogTrace("MarkVerificationFinished called");
    verificationCompleted.TrySetResult();
  }

  public Task<CompilationAfterParsing> LastDocument => TranslatedCompilation.ContinueWith(
    t => {
      if (t.IsCompletedSuccessfully) {
#pragma warning disable VSTHRD103
        logger.LogDebug($"LastDocument will return document version {t.Result.Version}");
        return verificationCompleted.Task.ContinueWith(
          verificationCompletedTask => {
            logger.LogDebug($"verificationCompleted finished with status {verificationCompletedTask.Status}");
            return Task.FromResult<CompilationAfterParsing>(t.Result);
          }, TaskScheduler.Current).Unwrap();
#pragma warning restore VSTHRD103
      }

      return ResolvedCompilation;
    }, TaskScheduler.Current).Unwrap();

  public async Task<TextEditContainer?> GetTextEditToFormatCode(Uri uri) {
    // TODO https://github.com/dafny-lang/dafny/issues/3416
    var parsedDocument = await ResolvedCompilation;
    if (parsedDocument.GetDiagnostics(uri).Any(diagnostic =>
          diagnostic.Level == ErrorLevel.Error &&
          diagnostic.Source == MessageSource.Parser
        )) {
      return null;
    }

    var firstToken = parsedDocument.Program.GetFirstTopLevelToken();
    if (firstToken == null) {
      return null;
    }
    var result = Formatting.__default.ReindentProgramFromFirstToken(firstToken,
      IndentationFormatter.ForProgram(parsedDocument.Program));

    var lastToken = firstToken;
    while (lastToken.Next != null) {
      lastToken = lastToken.Next;
    }
    // TODO: https://github.com/dafny-lang/dafny/issues/3415
    return new TextEditContainer(new TextEdit[] {
      // TODO end position doesn't take into account trailing trivia
      new() {NewText = result, Range = new Range(new Position(0,0), lastToken.GetLspPosition())}
    });

  }
}
