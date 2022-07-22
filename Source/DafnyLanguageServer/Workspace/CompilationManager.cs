using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
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
/// Manages the compilation of a single document version.
/// Agnostic to document updates. Does not handle migration of old document state.
/// </summary>
public class CompilationManager {

  private readonly ILogger logger;
  private readonly ITextDocumentLoader documentLoader;
  private readonly ICompilationStatusNotificationPublisher statusPublisher;
  private readonly IProgramVerifier verifier;

  private DafnyOptions Options => DafnyOptions.O;
  private VerifierOptions VerifierOptions { get; }

  public DocumentTextBuffer TextBuffer { get; }
  private readonly Range? lastChange;
  private readonly IServiceProvider services;
  private readonly ImmutableList<Position> migratedLastTouchedVerifiables;
  private bool shouldVerify;
  private readonly VerificationTree? migratedVerificationTree;

  private readonly IScheduler verificationUpdateScheduler = new EventLoopScheduler();
  private readonly ReplaySubject<DafnyDocument> documentUpdates = new();
  public IObservable<DafnyDocument> DocumentUpdates => documentUpdates;
  private readonly CancellationTokenSource cancellationSource;

  public Task<DafnyDocument> ResolvedDocument { get; }
  public Task<DafnyDocument> TranslatedDocument { get; }

  public CompilationManager(IServiceProvider services,
    VerifierOptions verifierOptions,
    DocumentTextBuffer textBuffer,
    Range? lastChange,
    bool shouldVerify,
    ImmutableList<Position> migratedLastTouchedVerifiables,
    VerificationTree? migratedVerificationTree) {
    VerifierOptions = verifierOptions;
    logger = services.GetRequiredService<ILogger<CompilationManager>>();
    documentLoader = services.GetRequiredService<ITextDocumentLoader>();
    verifier = services.GetRequiredService<IProgramVerifier>();
    statusPublisher = services.GetRequiredService<ICompilationStatusNotificationPublisher>();

    TextBuffer = textBuffer;
    this.services = services;
    this.migratedLastTouchedVerifiables = migratedLastTouchedVerifiables;
    this.shouldVerify = shouldVerify;
    this.migratedVerificationTree = migratedVerificationTree;
    this.lastChange = lastChange;
    cancellationSource = new();

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

  private async Task<DafnyDocument> ResolveAsync() {
    try {
      var resolvedDocument = await documentLoader.LoadAsync(TextBuffer, cancellationSource.Token);
      resolvedDocument.LastTouchedVerifiables = migratedLastTouchedVerifiables;
      resolvedDocument.VerificationTree = migratedVerificationTree ?? resolvedDocument.VerificationTree;
      documentLoader.PublishGutterIcons(resolvedDocument, false);
      documentUpdates.OnNext(resolvedDocument);
      return resolvedDocument;
    } catch (Exception e) {
      documentUpdates.OnError(e);
      throw;
    }
  }

  private async Task<DafnyDocument> TranslateAsync() {
    try {
      var resolvedDocument = await ResolvedDocument;
      var translatedDocument = await PrepareVerificationTasksAsync(resolvedDocument, cancellationSource.Token);
      documentUpdates.OnNext(translatedDocument);
      return translatedDocument;
    } catch (Exception e) {
      documentUpdates.OnError(e);
      throw;
    }
  }

  public async Task<DafnyDocument> PrepareVerificationTasksAsync(
    DafnyDocument loaded,
    CancellationToken cancellationToken) {
    if (loaded.ParseAndResolutionDiagnostics.Any(d =>
          d.Severity == DiagnosticSeverity.Error &&
          d.Source != MessageSource.Compiler.ToString() &&
          d.Source != MessageSource.Verifier.ToString())) {
      throw new TaskCanceledException();
    }

    var progressReporter = CreateVerificationProgressReporter(loaded);
    progressReporter.RecomputeVerificationTree();
    progressReporter.UpdateLastTouchedMethodPositions(lastChange);

    var verificationTasks = await verifier.GetVerificationTasksAsync(loaded, cancellationToken);
    if (VerifierOptions.GutterStatus) {
      progressReporter.ReportRealtimeDiagnostics(false, loaded);
      progressReporter.ReportImplementationsBeforeVerification(
        verificationTasks.Select(t => t.Implementation).ToArray());
    }

    var initialViews = new ConcurrentDictionary<ImplementationId, ImplementationView>();
    foreach (var task in verificationTasks) {
      var status = StatusFromBoogieStatus(task.CacheStatus);
      if (task.CacheStatus is Completed completed) {
        var view = new ImplementationView(task.Implementation.tok.GetLspRange(), status, GetDiagnosticsFromResult(loaded, completed.Result));
        initialViews.TryAdd(GetImplementationId(task.Implementation), view);
      } else {
        var view = new ImplementationView(task.Implementation.tok.GetLspRange(), status, Array.Empty<Diagnostic>());
        initialViews.TryAdd(GetImplementationId(task.Implementation), view);
      }
    }

    loaded.ImplementationIdToView = initialViews;
    loaded.Counterexamples = new();
    loaded.VerificationTasks = verificationTasks;
    var implementations = verificationTasks.Select(t => t.Implementation).ToHashSet();

    var subscription = verifier.BatchCompletions.Where(c =>
      implementations.Contains(c.Implementation)).Subscribe(progressReporter.ReportAssertionBatchResult);
    cancellationToken.Register(() => subscription.Dispose());
    loaded.GutterProgressReporter = progressReporter;
    return loaded;
  }

  protected virtual VerificationProgressReporter CreateVerificationProgressReporter(DafnyDocument document) {
    return new VerificationProgressReporter(
      services.GetRequiredService<ILogger<VerificationProgressReporter>>(),
      document, statusPublisher, this.services.GetRequiredService<INotificationPublisher>());
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

  private async Task VerifyAsync() {
    var translatedDocument = await TranslatedDocument;

    var implementationTasks = translatedDocument.VerificationTasks!;
    if (!implementationTasks.Any()) {
      MarkVerificationFinished();
    }

    statusPublisher.SendStatusNotification(translatedDocument.TextDocumentItem, CompilationStatus.VerificationStarted);

    foreach (var implementationTask in implementationTasks) {
      Verify(translatedDocument, implementationTask);
    }

    var lastDocument = await LastDocument;

    if (VerifierOptions.GutterStatus) {
      translatedDocument.GutterProgressReporter!.ReportRealtimeDiagnostics(true, lastDocument);
    }

    NotifyStatus(translatedDocument.TextDocumentItem, lastDocument, cancellationSource.Token);
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
    var id = GetImplementationId(implementationTask.Implementation);
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
        document.Counterexamples!.Push(counterExample);
      }

      var diagnostics = GetDiagnosticsFromResult(document, verificationResult);
      var view = new ImplementationView(implementationRange, status, diagnostics);
      document.ImplementationIdToView!.AddOrUpdate(id, view, (_, _) => view);
      if (VerifierOptions.GutterStatus) {
        document.GutterProgressReporter!.ReportEndVerifyImplementation(implementationTask.Implementation, verificationResult);
      }
    } else {
      document.ImplementationIdToView!.AddOrUpdate(id,
        _ => new ImplementationView(implementationRange, status, Array.Empty<Diagnostic>()),
        (_, previousView) => previousView with { Status = status });
    }

    documentUpdates.OnNext(document);
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

  // TODO migrate to higher level?
  private void NotifyStatus(TextDocumentItem item, DafnyDocument document, CancellationToken cancellationToken) {
    var errorCount = document.ImplementationIdToView!.Values.Sum(r => r.Diagnostics.Count(d => d.Severity == DiagnosticSeverity.Error));
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

  // TODO migrate to higher level?
  public Task<DafnyDocument> LastDocument => TranslatedDocument.ContinueWith(t => {
    if (t.IsCompletedSuccessfully) {
#pragma warning disable VSTHRD003
      return verificationCompleted.Task.ContinueWith(_ => t, TaskScheduler.Current).Unwrap();
#pragma warning restore VSTHRD003
    }

    return ResolvedDocument;
  }, TaskScheduler.Current).Unwrap();
}