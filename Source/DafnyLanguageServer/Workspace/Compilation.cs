using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive;
using System.Reactive.Concurrency;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Reactive.Threading.Tasks;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using VC;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

/// <summary>
/// The compilation of a single document version.
/// The document will be parsed, resolved, translated to Boogie and verified.
///
/// Compilation may be configured to pause after translation,
/// requiring a call to CompilationManager.Verify for the document to be verified.
///
/// Compilation is agnostic to document updates, it does not handle the migration of old document state.
/// </summary>
public class Compilation {

  private readonly ILogger logger;
  private readonly ITextDocumentLoader documentLoader;
  private readonly ICompilationStatusNotificationPublisher statusPublisher;
  private readonly INotificationPublisher notificationPublisher;
  private readonly IProgramVerifier verifier;

  public DocumentTextBuffer TextBuffer { get; }
  private readonly IServiceProvider services;

  // TODO CompilationManager shouldn't be aware of migration
  private readonly VerificationTree? migratedVerificationTree;

  private TaskCompletionSource started = new();
  private readonly IScheduler verificationUpdateScheduler = new EventLoopScheduler();
  private readonly CancellationTokenSource cancellationSource;
  private readonly Subject<Document> documentUpdates = new();
  public IObservable<Document> DocumentUpdates => documentUpdates;

  public Task<DocumentAfterParsing> ResolvedDocument { get; }
  public Task<DocumentAfterTranslation> TranslatedDocument { get; }

  public Compilation(IServiceProvider services,
    DocumentTextBuffer textBuffer,
    VerificationTree? migratedVerificationTree) {
    options = services.GetRequiredService<DafnyOptions>();
    logger = services.GetRequiredService<ILogger<Compilation>>();
    documentLoader = services.GetRequiredService<ITextDocumentLoader>();
    notificationPublisher = services.GetRequiredService<INotificationPublisher>();
    verifier = services.GetRequiredService<IProgramVerifier>();
    statusPublisher = services.GetRequiredService<ICompilationStatusNotificationPublisher>();

    TextBuffer = textBuffer;
    this.services = services;
    this.migratedVerificationTree = migratedVerificationTree;
    cancellationSource = new();

    MarkVerificationFinished();

    ResolvedDocument = ResolveAsync();
    TranslatedDocument = TranslateAsync();
  }

  public void Start() {
    started.TrySetResult();
  }

  private async Task<DocumentAfterParsing> ResolveAsync() {
    try {
      await started.Task;
      var documentAfterParsing = await documentLoader.LoadAsync(TextBuffer, cancellationSource.Token);

      // TODO, let gutter icon publications also used the published CompilationView.
      var state = documentAfterParsing.InitialIdeState(options);
      state = state with {
        VerificationTree = migratedVerificationTree ?? state.VerificationTree
      };
      notificationPublisher.PublishGutterIcons(state, false);

      logger.LogDebug($"documentUpdates.HasObservers: {documentUpdates.HasObservers}, threadId: {Thread.CurrentThread.ManagedThreadId}");
      documentUpdates.OnNext(documentAfterParsing);
      logger.LogDebug($"Passed documentAfterParsing to documentUpdates.OnNext, resolving ResolvedDocument task for version {documentAfterParsing.Version}.");
      return documentAfterParsing;

    } catch (Exception e) {
      documentUpdates.OnError(e);
      throw;
    }
  }

  private async Task<DocumentAfterTranslation> TranslateAsync() {
    var parsedCompilation = await ResolvedDocument;
    if (!options.Verify) {
      throw new OperationCanceledException();
    }
    if (parsedCompilation is not DocumentAfterResolution resolvedCompilation) {
      throw new OperationCanceledException();
    }

    try {
      var translatedDocument = await PrepareVerificationTasksAsync(resolvedCompilation, cancellationSource.Token);
      documentUpdates.OnNext(translatedDocument);
      foreach (var task in translatedDocument.VerificationTasks!) {
        cancellationSource.Token.Register(task.Cancel);
      }

      return translatedDocument;
    } catch (Exception e) {
      documentUpdates.OnError(e);
      throw;
    }
  }

  public async Task<DocumentAfterTranslation> PrepareVerificationTasksAsync(
    DocumentAfterResolution loaded,
    CancellationToken cancellationToken) {
    if (loaded.ParseAndResolutionDiagnostics.Any(d =>
          d.Level == ErrorLevel.Error &&
          d.Source != MessageSource.Compiler &&
          d.Source != MessageSource.Verifier)) {
      throw new TaskCanceledException();
    }

    var verificationTasks =
      await verifier.GetVerificationTasksAsync(loaded, cancellationToken);

    var initialViews = new Dictionary<ImplementationId, ImplementationView>();
    foreach (var task in verificationTasks) {
      var status = StatusFromBoogieStatus(task.CacheStatus);
      var implementationId = GetImplementationId(task.Implementation);
      try {
        if (task.CacheStatus is Completed completed) {
          var view = new ImplementationView(task.Implementation.tok.GetLspRange(), status,
            GetDiagnosticsFromResult(loaded, completed.Result).ToList());
          initialViews.Add(implementationId, view);
        } else {
          var view = new ImplementationView(task.Implementation.tok.GetLspRange(), status, Array.Empty<DafnyDiagnostic>());
          initialViews.Add(implementationId, view);
        }
      } catch (ArgumentException) {
        logger.LogCritical($"Two different implementation tasks have the same id, second name is {task.Implementation.Name}.");
      }
    }

    var translated = new DocumentAfterTranslation(services,
      loaded.TextDocumentItem, loaded.Program,
      loaded.ParseAndResolutionDiagnostics, loaded.SymbolTable, loaded.SignatureAndCompletionTable, loaded.GhostDiagnostics, verificationTasks,
      new(),
      initialViews,
      migratedVerificationTree ?? new DocumentVerificationTree(loaded.TextDocumentItem));

    translated.GutterProgressReporter.RecomputeVerificationTree();

    if (ReportGutterStatus) {
      translated.GutterProgressReporter.ReportRealtimeDiagnostics(false, translated);
    }
    translated.GutterProgressReporter.ReportImplementationsBeforeVerification(
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
    return new ImplementationId(implementation.tok.GetLspPosition(), prefix);
  }

  private void SetAllUnvisitedMethodsAsVerified(DocumentAfterTranslation document) {
    foreach (var tree in document.VerificationTree.Children) {
      tree.SetVerifiedIfPending();
    }
  }

  private int runningVerificationJobs = 0;
  public bool VerifyTask(DocumentAfterTranslation document, IImplementationTask implementationTask) {

    var statusUpdates = implementationTask.TryRun();
    if (statusUpdates == null) {
      if (implementationTask.CacheStatus is Completed completedCache) {
        foreach (var result in completedCache.Result.VCResults) {
          document.GutterProgressReporter.ReportVerifyImplementationRunning(implementationTask.Implementation);
          document.GutterProgressReporter.ReportAssertionBatchResult(
            new AssertionBatchResult(implementationTask.Implementation, result));
        }
        document.GutterProgressReporter.ReportEndVerifyImplementation(implementationTask.Implementation,
          completedCache.Result);
      }

      return false;
    }

    Interlocked.Increment(ref runningVerificationJobs);
    MarkVerificationStarted();
    statusUpdates.ObserveOn(verificationUpdateScheduler).Subscribe(
      update => {
        try {
          HandleStatusUpdate(document, implementationTask, update);
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
          logger.LogDebug($"Calling FinishedNotifications because there are no remaining verification jobs for version {document.Version}.");
          FinishedNotifications(document);
        }
      } catch (Exception e) {
        logger.LogCritical(e, "Caught exception while handling finally code of statusUpdates handler.");
      }
    }

    return true;
  }

  public void FinishedNotifications(DocumentAfterTranslation document) {
    MarkVerificationFinished();
    if (ReportGutterStatus) {
      // All unvisited trees need to set them as "verified"
      if (!cancellationSource.IsCancellationRequested) {
        SetAllUnvisitedMethodsAsVerified(document);
      }

      document.GutterProgressReporter.ReportRealtimeDiagnostics(true, document);
    }
  }

  private void HandleStatusUpdate(DocumentAfterTranslation document, IImplementationTask implementationTask, IVerificationStatus boogieStatus) {
    var id = GetImplementationId(implementationTask.Implementation);
    var status = StatusFromBoogieStatus(boogieStatus);
    var implementationRange = implementationTask.Implementation.tok.GetLspRange();
    logger.LogDebug($"Received status {boogieStatus} for {implementationTask.Implementation.Name}");
    if (boogieStatus is Running) {
      document.GutterProgressReporter.ReportVerifyImplementationRunning(implementationTask.Implementation);
    }

    if (boogieStatus is BatchCompleted batchCompleted) {
      document.GutterProgressReporter.ReportAssertionBatchResult(
        new AssertionBatchResult(implementationTask.Implementation, batchCompleted.VcResult));
    }

    if (boogieStatus is Completed completed) {
      var verificationResult = completed.Result;
      foreach (var counterExample in verificationResult.Errors) {
        document.Counterexamples.Add(counterExample);
      }
      // Sometimes, the boogie status is set as Completed
      // but the assertion batches were not reported yet.
      // because they are on a different thread.
      // This loop will ensure that every vc result has been dealt with
      // before we report that the verification of the implementation is finished 
      foreach (var result in completed.Result.VCResults) {
        document.GutterProgressReporter.ReportAssertionBatchResult(
          new AssertionBatchResult(implementationTask.Implementation, result));
      }

      var diagnostics = GetDiagnosticsFromResult(document, verificationResult).ToList();
      var view = new ImplementationView(implementationRange, status, diagnostics);
      document.ImplementationIdToView[id] = view;
      document.GutterProgressReporter.ReportEndVerifyImplementation(implementationTask.Implementation, verificationResult);
    } else {
      var existingView = document.ImplementationIdToView.GetValueOrDefault(id) ??
                         new ImplementationView(implementationRange, status, Array.Empty<DafnyDiagnostic>());
      document.ImplementationIdToView[id] = existingView with { Status = status };
    }

    documentUpdates.OnNext(document);
  }

  private bool ReportGutterStatus => options.Get(ServerCommand.LineVerificationStatus);

  private List<DafnyDiagnostic> GetDiagnosticsFromResult(Document document, VerificationResult result) {
    var errorReporter = new DiagnosticErrorReporter(options, document.TextDocumentItem.Text, document.Uri);
    foreach (var counterExample in result.Errors) {
      errorReporter.ReportBoogieError(counterExample.CreateErrorInformation(result.Outcome, options.ForceBplErrors));
    }

    var outcomeError = result.GetOutcomeError(options);
    if (outcomeError != null) {
      errorReporter.ReportBoogieError(outcomeError);
    }

    var diagnostics = errorReporter.GetDiagnostics(document.Uri);
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
      default:
        throw new ArgumentOutOfRangeException();
    }
  }

  public void CancelPendingUpdates() {
    cancellationSource.Cancel();
  }

  private TaskCompletionSource verificationCompleted = new();
  private readonly DafnyOptions options;

  public void MarkVerificationStarted() {
    logger.LogDebug("MarkVerificationStarted called");
    if (verificationCompleted.Task.IsCompleted) {
      verificationCompleted = new TaskCompletionSource();
    }
  }

  public void MarkVerificationFinished() {
    logger.LogDebug("MarkVerificationFinished called");
    verificationCompleted.TrySetResult();
  }

  public Task<DocumentAfterParsing> LastDocument => TranslatedDocument.ContinueWith(
    t => {
      if (t.IsCompletedSuccessfully) {
#pragma warning disable VSTHRD103
        logger.LogDebug($"LastDocument will return document version {t.Result.Version}");
        return verificationCompleted.Task.ContinueWith(
          verificationCompletedTask => {
            logger.LogDebug($"verificationCompleted finished with status {verificationCompletedTask.Status}");
            return Task.FromResult<DocumentAfterParsing>(t.Result);
          }, TaskScheduler.Current).Unwrap();
#pragma warning restore VSTHRD103
      }

      return ResolvedDocument;
    }, TaskScheduler.Current).Unwrap();

  public async Task<TextEditContainer?> GetTextEditToFormatCode() {
    // TODO https://github.com/dafny-lang/dafny/issues/3416
    var parsedDocument = await ResolvedDocument;
    if (parsedDocument.Diagnostics.Any(diagnostic =>
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

    // TODO: https://github.com/dafny-lang/dafny/issues/3415
    return new TextEditContainer(new TextEdit[] {
      new() {NewText = result, Range = parsedDocument.TextDocumentItem.Range}
    });

  }
}
