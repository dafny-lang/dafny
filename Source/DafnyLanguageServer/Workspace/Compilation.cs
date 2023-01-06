using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive;
using System.Reactive.Concurrency;
using System.Reactive.Linq;
using System.Reactive.Subjects;
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
  private readonly IDafnyParser parser;

  public DocumentTextBuffer TextBuffer { get; }
  private readonly IServiceProvider services;

  // TODO CompilationManager shouldn't be aware of migration
  private readonly VerificationTree? migratedVerificationTree;

  private TaskCompletionSource started = new();
  private readonly IScheduler verificationUpdateScheduler = new EventLoopScheduler();
  private readonly CancellationTokenSource cancellationSource;
  private readonly Subject<Document> documentUpdates = new();
  public IObservable<Document> DocumentUpdates => documentUpdates;

  public Task<DocumentAfterParsing> ParsedDocument { get; }
  public Task<DocumentAfterResolution> ResolvedDocument { get; }
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
    parser = services.GetRequiredService<IDafnyParser>();

    TextBuffer = textBuffer;
    this.services = services;
    this.migratedVerificationTree = migratedVerificationTree;
    cancellationSource = new();

    MarkVerificationFinished();

    ParsedDocument = ParseAsync();
    ResolvedDocument = ResolveAsync();
    TranslatedDocument = TranslateAsync();
  }

  public void Start() {
    started.TrySetResult();
  }

  private async Task<DocumentAfterParsing> ParseAsync() {
    try {
      await started.Task;

      var errorReporter = new DiagnosticErrorReporter(TextBuffer.Text, TextBuffer.Uri);
      statusPublisher.SendStatusNotification(TextBuffer, CompilationStatus.ResolutionStarted);
      var program = parser.Parse(TextBuffer, errorReporter, cancellationSource.Token);
      var documentAfterParsing = new DocumentAfterParsing(TextBuffer, program, errorReporter.GetDiagnostics(TextBuffer.Uri));
      if (errorReporter.HasErrors) {
        documentUpdates.OnNext(documentAfterParsing);
        statusPublisher.SendStatusNotification(TextBuffer, CompilationStatus.ParsingFailed);
      }

      return documentAfterParsing;
    } catch (Exception e) {
      documentUpdates.OnError(e);
      throw;
    }
  }

  private async Task<DocumentAfterResolution> ResolveAsync() {
    var parsedDocument = await ParsedDocument;
    if (parsedDocument.Diagnostics.Any()) {
      throw new OperationCanceledException();
    }

    try {
      var documentAfterResolution = await documentLoader.LoadAsync(parsedDocument, cancellationSource.Token);

      // TODO, let gutter icon publications also used the published CompilationView.
      var state = parsedDocument.InitialIdeState();
      state = state with {
        VerificationTree = migratedVerificationTree ?? state.VerificationTree
      };
      notificationPublisher.PublishGutterIcons(state, false);

      logger.LogDebug($"documentUpdates.HasObservers: {documentUpdates.HasObservers}, threadId: {Thread.CurrentThread.ManagedThreadId}");
      documentUpdates.OnNext(documentAfterResolution);
      logger.LogDebug($"Passed documentAfterParsing to documentUpdates.OnNext, resolving ResolvedDocument task for version {parsedDocument.Version}.");
      return documentAfterResolution;

    } catch (Exception e) {
      documentUpdates.OnError(e);
      throw;
    }
  }

  private async Task<DocumentAfterTranslation> TranslateAsync() {
    var resolvedCompilation = await ResolvedDocument;

    if (resolvedCompilation.ParseAndResolutionDiagnostics.Any(d =>
          d.Severity == DiagnosticSeverity.Error &&
          d.Source != MessageSource.Compiler.ToString() &&
          d.Source != MessageSource.Verifier.ToString())) {
      throw new TaskCanceledException();
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

    var verificationTasks =
      await verifier.GetVerificationTasksAsync(loaded, cancellationToken);

    var initialViews = new Dictionary<ImplementationId, ImplementationView>();
    foreach (var task in verificationTasks) {
      var status = StatusFromBoogieStatus(task.CacheStatus);
      var implementationId = GetImplementationId(task.Implementation);
      try {
        if (task.CacheStatus is Completed completed) {
          var view = new ImplementationView(task.Implementation.tok.GetLspRange(), status,
            GetDiagnosticsFromResult(loaded, completed.Result));
          initialViews.Add(implementationId, view);
        } else {
          var view = new ImplementationView(task.Implementation.tok.GetLspRange(), status, Array.Empty<Diagnostic>());
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

    var implementations = verificationTasks.Select(t => t.Implementation).ToHashSet();

    var subscription = verifier.BatchCompletions.ObserveOn(verificationUpdateScheduler).Where(c =>
      implementations.Contains(c.Implementation)).Subscribe(translated.GutterProgressReporter.ReportAssertionBatchResult);
    cancellationToken.Register(() => subscription.Dispose());
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

    if (boogieStatus is Completed completed) {
      var verificationResult = completed.Result;
      foreach (var counterExample in verificationResult.Errors) {
        document.Counterexamples.Add(counterExample);
      }

      var diagnostics = GetDiagnosticsFromResult(document, verificationResult);
      var view = new ImplementationView(implementationRange, status, diagnostics);
      document.ImplementationIdToView[id] = view;
      document.GutterProgressReporter.ReportEndVerifyImplementation(implementationTask.Implementation, verificationResult);
    } else {
      var existingView = document.ImplementationIdToView.GetValueOrDefault(id) ??
                         new ImplementationView(implementationRange, status, Array.Empty<Diagnostic>());
      document.ImplementationIdToView[id] = existingView with { Status = status };
    }

    documentUpdates.OnNext(document);
  }

  private bool ReportGutterStatus => options.Get(ServerCommand.LineVerificationStatus);

  private List<Diagnostic> GetDiagnosticsFromResult(Document document, VerificationResult result) {
    var errorReporter = new DiagnosticErrorReporter(document.TextDocumentItem.Text, document.Uri);
    foreach (var counterExample in result.Errors) {
      errorReporter.ReportBoogieError(counterExample.CreateErrorInformation(result.Outcome, options.ForceBplErrors));
    }

    var outcomeError = result.GetOutcomeError(options);
    if (outcomeError != null) {
      errorReporter.ReportBoogieError(outcomeError);
    }

    return errorReporter.GetDiagnostics(document.Uri).OrderBy(d => d.Range.Start).ToList();
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

  public Task<DocumentAfterResolution> LastDocument => TranslatedDocument.ContinueWith(
    t => {
      if (t.IsCompletedSuccessfully) {
#pragma warning disable VSTHRD103
        logger.LogDebug($"LastDocument will return document version {t.Result.Version}");
        return verificationCompleted.Task.ContinueWith(
          verificationCompletedTask => {
            logger.LogDebug($"verificationCompleted finished with status {verificationCompletedTask.Status}");
            return Task.FromResult<DocumentAfterResolution>(t.Result);
          }, TaskScheduler.Current).Unwrap();
#pragma warning restore VSTHRD103
      }

      return ResolvedDocument;
    }, TaskScheduler.Current).Unwrap();
}
