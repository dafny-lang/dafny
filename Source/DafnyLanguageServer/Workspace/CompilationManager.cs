using System;
using System.Collections.Generic;
using System.Data;
using System.Linq;
using System.Reactive.Concurrency;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using VC;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class CompilationManager {

  private readonly ILogger logger;
  private readonly ITelemetryPublisher telemetryPublisher;
  private readonly INotificationPublisher notificationPublisher;
  private readonly ITextDocumentLoader documentLoader;
  private readonly ITextChangeProcessor textChangeProcessor;
  private readonly IRelocator relocator;
  private readonly ICompilationStatusNotificationPublisher statusPublisher;

  private DafnyOptions Options => DafnyOptions.O;
  private readonly DocumentOptions options;
  private VerifierOptions VerifierOptions { get; }

  public DocumentTextBuffer TextBuffer { get; }
  private bool shouldVerify;

  private DafnyDocument lastDocumentUpdate;
  private readonly IScheduler verificationUpdateScheduler = new EventLoopScheduler();
  private readonly ReplaySubject<DafnyDocument> documentUpdates = new();
  public IObservable<DafnyDocument> DocumentUpdates => documentUpdates;
  private readonly CancellationTokenSource cancellationSource;

  public Task<DafnyDocument> ResolvedDocument { get; }
  public Task<DafnyDocument> TranslatedDocument { get; }

  public CompilationManager(IServiceProvider services, DocumentTextBuffer textBuffer, bool shouldVerify) {
    telemetryPublisher = services.GetRequiredService<ITelemetryPublisher>();
    logger = services.GetRequiredService<ILogger>();
    notificationPublisher = services.GetRequiredService<INotificationPublisher>();
    documentLoader = services.GetRequiredService<ITextDocumentLoader>();
    textChangeProcessor = services.GetRequiredService<ITextChangeProcessor>();
    relocator = services.GetRequiredService<IRelocator>();
    statusPublisher = services.GetRequiredService<ICompilationStatusNotificationPublisher>();

    this.TextBuffer = textBuffer;
    this.shouldVerify = shouldVerify;
    cancellationSource = new();

    lastDocumentUpdate = documentLoader.CreateUnloaded(textBuffer, CancellationToken.None);
    documentUpdates.Subscribe(next => lastDocumentUpdate = next);

    ResolvedDocument = ResolveAsync();
    TranslatedDocument = TranslateAsync();

    if (shouldVerify) {
      var _ = VerifyAsync();
    } else {
      MarkVerificationFinished();
    }
  }

  public void Verify() {
    if (shouldVerify) {
      return;
    }

    shouldVerify = true;
    MarkVerificationStarted();
    var _ = VerifyAsync();
  }

  private void PublishUnhandledException(Exception exception)
  {
    var previousDiagnostics = lastDocumentUpdate.LoadCanceled
      ? new Diagnostic[] { }
      : lastDocumentUpdate.ParseAndResolutionDiagnostics;
    documentUpdates.OnNext(lastDocumentUpdate with
    {
      LoadCanceled = false,
      ParseAndResolutionDiagnostics = previousDiagnostics.Concat(new Diagnostic[]
      {
        new()
        {
          Message =
            "Dafny encountered an internal error. Please report it at <https://github.com/dafny-lang/dafny/issues>.\n" +
            exception,
          Severity = DiagnosticSeverity.Error,
          Range = lastDocumentUpdate.Program.GetFirstTopLevelToken().GetLspRange(),
          Source = "Crash"
        }
      }).ToList()
    });
    telemetryPublisher.PublishUnhandledException(exception);
  }

  private async Task<DafnyDocument> ResolveAsync() {
    try {
      var resolvedDocument = await documentLoader.LoadAsync(TextBuffer, cancellationSource.Token);
      documentLoader.PublishGutterIcons(resolvedDocument, false);
      documentUpdates.OnNext(resolvedDocument.Snapshot());
      return resolvedDocument;
    } catch (OperationCanceledException) {
      throw;
    } catch (Exception exception) {
      PublishUnhandledException(exception);
      throw;
    }
  }

  private async Task<DafnyDocument> TranslateAsync() {

    try {
      var resolvedDocument = await ResolvedDocument;
      var translatedDocument = await documentLoader.PrepareVerificationTasksAsync(resolvedDocument, cancellationSource.Token);
      documentUpdates.OnNext(translatedDocument.Snapshot());
      return translatedDocument;
    } catch (OperationCanceledException) {
      throw;
    } catch (Exception exception) {
      PublishUnhandledException(exception);
      throw;
    }
  }

  private async Task VerifyAsync() {
    var translatedDocument = await TranslatedDocument;

    var implementationTasks = translatedDocument.VerificationTasks!;
    if (!implementationTasks.Any()) {
      MarkVerificationFinished();
      return;
    }

    statusPublisher.SendStatusNotification(translatedDocument.TextDocumentItem, CompilationStatus.VerificationStarted);

    foreach (var implementationTask in implementationTasks) {
      Verify(translatedDocument, implementationTask);
    }

    var lastDocument = await LastDocument;

    if (VerifierOptions.GutterStatus) {
      translatedDocument.GutterProgressReporter!.ReportRealtimeDiagnostics(true, lastDocument);
    }

    NotifyStatusAsync(translatedDocument.TextDocumentItem, lastDocument, cancellationSource.Token);
  }

    public bool Verify(DafnyDocument dafnyDocument, IImplementationTask implementationTask) {

      var statusUpdates = implementationTask.TryRun();
      if (statusUpdates == null) {
        if (VerifierOptions.GutterStatus && implementationTask.CacheStatus is Completed completedCache) {
          foreach (var result in completedCache.Result.VCResults) {
            dafnyDocument.GutterProgressReporter!.ReportAssertionBatchResult(
              new AssertionBatchResult(implementationTask.Implementation, result));
          }

          dafnyDocument.GutterProgressReporter!.ReportEndVerifyImplementation(implementationTask.Implementation,
            completedCache.Result);
        }

        return false;
      }

      MarkVerificationStarted();
      statusUpdates.ObserveOn(verificationUpdateScheduler).Subscribe(
        update => HandleStatusUpdate(dafnyDocument, implementationTask, update),
        () => {
          if (dafnyDocument.VerificationTasks!.All(t => t.IsIdle)) {
            MarkVerificationFinished();
          }
        });

      return true;
    }

    private void HandleStatusUpdate(DafnyDocument document, IImplementationTask implementationTask, IVerificationStatus boogieStatus) {
      var id = TextDocumentLoader.GetImplementationId(implementationTask.Implementation);
      var status = StatusFromBoogieStatus(boogieStatus);
      var implementationRange = implementationTask.Implementation.tok.GetLspRange();
      if (boogieStatus is Running) {
        if (VerifierOptions.GutterStatus) {
          document.GutterProgressReporter!.ReportVerifyImplementationRunning(implementationTask.Implementation);
        }
      }

      if (boogieStatus is Completed completed) {
        var verificationResult = completed.Result;
        foreach (var counterExample in verificationResult.Errors) {
          document.Counterexamples.Push(counterExample);
        }

        var diagnostics = GetDiagnosticsFromResult(document, verificationResult);
        var view = new ImplementationView(implementationRange, status, diagnostics);
        document.ImplementationIdToView.AddOrUpdate(id, view, (_, _) => view);
        if (VerifierOptions.GutterStatus) {
          document.GutterProgressReporter!.ReportEndVerifyImplementation(implementationTask.Implementation, verificationResult);
        }
      } else {
        document.ImplementationIdToView.AddOrUpdate(id,
          _ => new ImplementationView(implementationRange, status, Array.Empty<Diagnostic>()),
          (_, previousView) => previousView with { Status = status });
      }

      documentUpdates.OnNext(document.Snapshot());
    }

    private List<Diagnostic> GetDiagnosticsFromResult(DafnyDocument document, VerificationResult result) {
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

    private PublishedVerificationStatus StatusFromBoogieStatus(IVerificationStatus verificationStatus) {
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

  private void NotifyStatusAsync(TextDocumentItem item, DafnyDocument document, CancellationToken cancellationToken) {
    var errorCount = document.ImplementationIdToView.Values.Sum(r => r.Diagnostics.Count(d => d.Severity == DiagnosticSeverity.Error));
    logger.LogDebug($"Finished verification with {errorCount} errors.");
    var verified = errorCount == 0;
    var compilationStatusAfterVerification = verified
      ? CompilationStatus.VerificationSucceeded
      : CompilationStatus.VerificationFailed;
    statusPublisher.SendStatusNotification(item, compilationStatusAfterVerification,
      cancellationToken.IsCancellationRequested ? "(cancelled)" : null);
  }

  public void CancelPendingUpdates() {
    MarkVerificationFinished();
    cancellationSource.Cancel();
  }

  public bool Idle => verificationCompleted.Task.IsCompleted;

  private TaskCompletionSource verificationCompleted = new();
  public void MarkVerificationStarted() {
    if (verificationCompleted.Task.IsCompleted) {
      verificationCompleted = new TaskCompletionSource();
    }
  }

  public void MarkVerificationFinished() {
    verificationCompleted.TrySetResult();
  }

  public Task<DafnyDocument> LastDocument => TranslatedDocument.ContinueWith(t => {
    if (t.IsCompletedSuccessfully) {
#pragma warning disable VSTHRD003
      return verificationCompleted.Task.ContinueWith(_ => t, TaskScheduler.Current).Unwrap();
#pragma warning restore VSTHRD003
    }

    return ResolvedDocument;
  }, TaskScheduler.Current).Unwrap();
}