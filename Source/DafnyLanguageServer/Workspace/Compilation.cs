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

  private DafnyOptions Options => DafnyOptions.O;
  private VerifierOptions VerifierOptions { get; }

  public DocumentTextBuffer TextBuffer { get; }
  private readonly IServiceProvider services;

  // TODO CompilationManager shouldn't be aware of migration
  private readonly VerificationTree? migratedVerificationTree;

  private readonly IScheduler verificationUpdateScheduler = new EventLoopScheduler();
  private readonly CancellationTokenSource cancellationSource;
  private readonly ReplaySubject<Document> documentUpdates = new();
  public IObservable<Document> DocumentUpdates => documentUpdates;

  public Task<DocumentAfterParsing> ResolvedDocument { get; }
  public Task<DocumentAfterTranslation> TranslatedDocument { get; }

  public Compilation(IServiceProvider services,
    VerifierOptions verifierOptions,
    DocumentTextBuffer textBuffer,
    VerificationTree? migratedVerificationTree) {
    VerifierOptions = verifierOptions;
    logger = services.GetRequiredService<ILogger<Compilation>>();
    documentLoader = services.GetRequiredService<ITextDocumentLoader>();
    notificationPublisher = services.GetRequiredService<INotificationPublisher>();
    verifier = services.GetRequiredService<IProgramVerifier>();
    statusPublisher = services.GetRequiredService<ICompilationStatusNotificationPublisher>();

    TextBuffer = textBuffer;
    this.services = services;
    this.migratedVerificationTree = migratedVerificationTree;
    cancellationSource = new();

    ResolvedDocument = ResolveAsync();
    TranslatedDocument = TranslateAsync();
  }

  private async Task<DocumentAfterParsing> ResolveAsync() {
    try {
      var parsedCompilation = await documentLoader.LoadAsync(TextBuffer, cancellationSource.Token);

      // TODO, let gutter icon publications also used the published CompilationView.
      var state = parsedCompilation.InitialIdeState();
      state = state with {
        VerificationTree = migratedVerificationTree ?? state.VerificationTree
      };
      notificationPublisher.PublishGutterIcons(state, false);

      documentUpdates.OnNext(parsedCompilation);
      return parsedCompilation;

    } catch (Exception e) {
      documentUpdates.OnError(e);
      throw;
    }
  }

  private async Task<DocumentAfterTranslation> TranslateAsync() {
    var parsedCompilation = await ResolvedDocument;
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
          d.Severity == DiagnosticSeverity.Error &&
          d.Source != MessageSource.Compiler.ToString() &&
          d.Source != MessageSource.Verifier.ToString())) {
      throw new TaskCanceledException();
    }

    var verificationTasks =
      await verifier.GetVerificationTasksAsync(loaded, cancellationToken);

    var initialViews = new Dictionary<ImplementationId, ImplementationView>();
    foreach (var task in verificationTasks) {
      var status = StatusFromBoogieStatus(task.CacheStatus);
      if (task.CacheStatus is Completed completed) {
        var view = new ImplementationView(task.Implementation.tok.GetLspRange(), status, GetDiagnosticsFromResult(loaded, completed.Result));
        initialViews.Add(GetImplementationId(task.Implementation), view);
      } else {
        var view = new ImplementationView(task.Implementation.tok.GetLspRange(), status, Array.Empty<Diagnostic>());
        initialViews.Add(GetImplementationId(task.Implementation), view);
      }
    }

    var translated = new DocumentAfterTranslation(services,
      loaded.TextDocumentItem, loaded.Program,
      loaded.ParseAndResolutionDiagnostics, loaded.SymbolTable, loaded.GhostDiagnostics, verificationTasks,
      new(),
      initialViews,
      migratedVerificationTree ?? new DocumentVerificationTree(loaded.TextDocumentItem));

    translated.GutterProgressReporter.RecomputeVerificationTree();

    if (VerifierOptions.GutterStatus) {
      translated.GutterProgressReporter.ReportRealtimeDiagnostics(false, translated);
      translated.GutterProgressReporter.ReportImplementationsBeforeVerification(
        verificationTasks.Select(t => t.Implementation).ToArray());
    }

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

  public bool VerifyTask(DocumentAfterTranslation document, IImplementationTask implementationTask) {

    var statusUpdates = implementationTask.TryRun();
    if (statusUpdates == null) {
      if (VerifierOptions.GutterStatus && implementationTask.CacheStatus is Completed completedCache) {
        foreach (var result in completedCache.Result.VCResults) {
          document.GutterProgressReporter.ReportAssertionBatchResult(
            new AssertionBatchResult(implementationTask.Implementation, result));
        }

        document.GutterProgressReporter.ReportEndVerifyImplementation(implementationTask.Implementation,
          completedCache.Result);
      }

      return false;
    }

    MarkVerificationStarted();
    statusUpdates.Catch<IVerificationStatus, Exception>(e => {
      logger.LogError(e, "Caught error in statusUpdates observable.");
      return Observable.Empty<IVerificationStatus>();
    }).ObserveOn(verificationUpdateScheduler).Subscribe(
      update => {
        try {
          HandleStatusUpdate(document, implementationTask, update);
        } catch (Exception e) {
          logger.LogCritical(e, "Caught exception in statusUpdates OnNext.");
        }
      },
      () => {
        try {
          if (document.VerificationTasks!.All(t => t.IsIdle)) {
            FinishedNotifications(document);
          }
        } catch (Exception e) {
          logger.LogCritical(e, "Caught exception in statusUpdates OnCompleted.");
        }
      });

    return true;
  }

  public void FinishedNotifications(DocumentAfterTranslation document) {
    MarkVerificationFinished();
    if (VerifierOptions.GutterStatus) {
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
      if (VerifierOptions.GutterStatus) {
        document.GutterProgressReporter.ReportVerifyImplementationRunning(implementationTask.Implementation);
      }
    }

    if (boogieStatus is Completed completed) {
      var verificationResult = completed.Result;
      foreach (var counterExample in verificationResult.Errors) {
        document.Counterexamples.Add(counterExample);
      }

      var diagnostics = GetDiagnosticsFromResult(document, verificationResult);
      var view = new ImplementationView(implementationRange, status, diagnostics);
      document.ImplementationIdToView[id] = view;
      if (VerifierOptions.GutterStatus) {
        document.GutterProgressReporter.ReportEndVerifyImplementation(implementationTask.Implementation, verificationResult);
      }
      logger.LogInformation($"Verification of Boogie implementation {implementationTask.Implementation.Name} completed.");
    } else {
      var existingView = document.ImplementationIdToView.GetValueOrDefault(id) ??
                         new ImplementationView(implementationRange, status, Array.Empty<Diagnostic>());
      document.ImplementationIdToView[id] = existingView with { Status = status };
    }

    documentUpdates.OnNext(document);
  }

  private List<Diagnostic> GetDiagnosticsFromResult(Document document, VerificationResult result) {
    var errorReporter = new DiagnosticErrorReporter(document.TextDocumentItem.Text, document.Uri);
    foreach (var counterExample in result.Errors) {
      errorReporter.ReportBoogieError(counterExample.CreateErrorInformation(result.Outcome, Options.ForceBplErrors));
    }

    var outcomeError = result.GetOutcomeError(Options);
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
    MarkVerificationFinished();
    cancellationSource.Cancel();
  }

  private TaskCompletionSource verificationCompleted = new();

  public void MarkVerificationStarted() {
    if (verificationCompleted.Task.IsCompleted) {
      verificationCompleted = new TaskCompletionSource();
    }
  }

  public void MarkVerificationFinished() {
    verificationCompleted.TrySetResult();
  }

  public Task<DocumentAfterParsing> LastDocument => TranslatedDocument.ContinueWith(
    t => {
      if (t.IsCompletedSuccessfully) {
        return verificationCompleted.Task.ContinueWith(
#pragma warning disable VSTHRD103
          _ => Task.FromResult<DocumentAfterParsing>(t.Result), TaskScheduler.Current).Unwrap();
#pragma warning restore VSTHRD103
      }

      return ResolvedDocument;
    }, TaskScheduler.Current).Unwrap();
}
