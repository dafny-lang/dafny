using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive.Concurrency;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using IntervalTree;
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
/// The document will be parsed, resolved, translated to Boogie and verified.
///
/// CompilationManager may be configured to pause after translation,
/// requiring a call to CompilationManager.Verify for the document to be verified.
///
/// CompilationManager is agnostic to document updates, it does not handle the migration of old document state.
/// </summary>
public class CompilationManager {

  private readonly ILogger logger;
  private readonly ITextDocumentLoader documentLoader;
  private readonly ICompilationStatusNotificationPublisher statusPublisher;
  private readonly INotificationPublisher notificationPublisher;
  private readonly IProgramVerifier verifier;

  private DafnyOptions Options => DafnyOptions.O;
  private VerifierOptions VerifierOptions { get; }

  public DocumentTextBuffer TextBuffer { get; }
  private readonly IServiceProvider services;

  private readonly bool verifyAllImmediately;
  private readonly IEnumerable<Range> changedRanges;

  // TODO replace
  private readonly VerificationTree? migratedVerificationTree;

  private readonly IScheduler verificationUpdateScheduler = new EventLoopScheduler();
  private readonly CancellationTokenSource cancellationSource;
  private readonly ReplaySubject<Compilation> documentUpdates = new();
  public IObservable<Compilation> DocumentUpdates => documentUpdates;

  public Task<CompilationAfterParsing> ResolvedDocument { get; }
  public Task<CompilationAfterTranslation> TranslatedDocument { get; }

  public CompilationManager(IServiceProvider services,
    VerifierOptions verifierOptions,
    DocumentTextBuffer textBuffer,
    bool verifyAllImmediately,
    IReadOnlyList<Range> changedRanges,
    VerificationTree? migratedVerificationTree) {
    VerifierOptions = verifierOptions;
    logger = services.GetRequiredService<ILogger<CompilationManager>>();
    documentLoader = services.GetRequiredService<ITextDocumentLoader>();
    notificationPublisher = services.GetRequiredService<INotificationPublisher>();
    verifier = services.GetRequiredService<IProgramVerifier>();
    statusPublisher = services.GetRequiredService<ICompilationStatusNotificationPublisher>();

    TextBuffer = textBuffer;
    this.services = services;
    this.verifyAllImmediately = verifyAllImmediately;
    this.changedRanges = changedRanges;
    this.migratedVerificationTree = migratedVerificationTree;
    cancellationSource = new();

    ResolvedDocument = ResolveAsync();
    TranslatedDocument = TranslateAsync();

    if (verifyAllImmediately) {
      var _ = VerifyEverythingAsync();
    } else {
      MarkVerificationFinished();
    }
  }

  public void VerifyAll() {
    if (verifyAllImmediately) {
      return;
    }

    MarkVerificationStarted();
    var _ = VerifyEverythingAsync();
  }

  private async Task<CompilationAfterParsing> ResolveAsync() {
    try {
      var parsedCompilation = await documentLoader.LoadAsync(TextBuffer, cancellationSource.Token);

      // TODO, let gutter icon publications also used the published CompilationView.
      var compilationView = parsedCompilation.Snapshot();
      compilationView = compilationView with {
        VerificationTree = migratedVerificationTree ?? compilationView.VerificationTree
      };
      notificationPublisher.PublishGutterIcons(compilationView, false);

      documentUpdates.OnNext(parsedCompilation);
      return parsedCompilation;

    } catch (Exception e) {
      documentUpdates.OnError(e);
      throw;
    }
  }

  private async Task<CompilationAfterTranslation> TranslateAsync() {
    var parsedCompilation = await ResolvedDocument;
    if (parsedCompilation is not CompilationAfterResolution resolvedCompilation) {
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

  public async Task<CompilationAfterTranslation> PrepareVerificationTasksAsync(
    CompilationAfterResolution loaded,
    CancellationToken cancellationToken) {
    if (loaded.ParseAndResolutionDiagnostics.Any(d =>
          d.Severity == DiagnosticSeverity.Error &&
          d.Source != MessageSource.Compiler.ToString() &&
          d.Source != MessageSource.Verifier.ToString())) {
      throw new TaskCanceledException();
    }

    var tree = new DocumentVerificationTree(loaded.TextDocumentItem);
    VerificationProgressReporter.UpdateTree(loaded, tree);
    var intervalTree = new IntervalTree<Position, Position>();
    foreach (var childTree in tree.Children) {
      intervalTree.Add(childTree.Range.Start, childTree.Range.End, childTree.Position);
    }

    var verifiableToPosition = changedRanges.
      SelectMany(changeRange => intervalTree.Query(changeRange.Start, changeRange.End)).
      Distinct().Select((position, i) => (position, i)).
      ToDictionary(k => k.position, k => k.i);

    var verificationTasks =
      await verifier.GetVerificationTasksAsync(loaded, verifiableToPosition, cancellationToken);

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

    var translated = new CompilationAfterTranslation(services,
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

  private async Task VerifyEverythingAsync() {
    var translatedDocument = await TranslatedDocument;

    var implementationTasks = translatedDocument.VerificationTasks!;
    if (!implementationTasks.Any()) {
      FinishedNotifications(translatedDocument);
    }

    statusPublisher.SendStatusNotification(translatedDocument.TextDocumentItem, CompilationStatus.VerificationStarted);

    foreach (var implementationTask in implementationTasks) {
      VerifyTask(translatedDocument, implementationTask);
    }
  }

  private void SetAllUnvisitedMethodsAsVerified(CompilationAfterTranslation document) {
    foreach (var tree in document.VerificationTree.Children) {
      tree.SetVerifiedIfPending();
    }
  }

  public bool VerifyTask(CompilationAfterTranslation dafnyDocument, IImplementationTask implementationTask) {

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
          FinishedNotifications(dafnyDocument);
        }
      });

    return true;
  }

  private void FinishedNotifications(CompilationAfterTranslation dafnyDocument) {
    MarkVerificationFinished();
    if (VerifierOptions.GutterStatus) {
      // All unvisited trees need to set them as "verified"
      if (!cancellationSource.IsCancellationRequested) {
        SetAllUnvisitedMethodsAsVerified(dafnyDocument);
      }

      dafnyDocument.GutterProgressReporter!.ReportRealtimeDiagnostics(true, dafnyDocument);
    }

    NotifyStatus(dafnyDocument.TextDocumentItem, dafnyDocument, cancellationSource.Token);
  }

  private void HandleStatusUpdate(CompilationAfterTranslation document, IImplementationTask implementationTask, IVerificationStatus boogieStatus) {
    var id = GetImplementationId(implementationTask.Implementation);
    var status = StatusFromBoogieStatus(boogieStatus);
    var implementationRange = implementationTask.Implementation.tok.GetLspRange();
    logger.LogDebug($"Received status {boogieStatus} for {implementationTask.Implementation.Name}");
    if (boogieStatus is Running) {
      if (VerifierOptions.GutterStatus) {
        document.GutterProgressReporter!.ReportVerifyImplementationRunning(implementationTask.Implementation);
      }
    }

    if (boogieStatus is Completed completed) {
      var verificationResult = completed.Result;
      foreach (var counterExample in verificationResult.Errors) {
        document.Counterexamples!.Add(counterExample);
      }

      var diagnostics = GetDiagnosticsFromResult(document, verificationResult);
      var view = new ImplementationView(implementationRange, status, diagnostics);
      document.ImplementationIdToView![id] = view;
      if (VerifierOptions.GutterStatus) {
        document.GutterProgressReporter!.ReportEndVerifyImplementation(implementationTask.Implementation, verificationResult);
      }
      logger.LogInformation($"Verification of Boogie implementation {implementationTask.Implementation.Name} completed.");
    } else {
      var existingView = document.ImplementationIdToView!.GetValueOrDefault(id) ??
                         new ImplementationView(implementationRange, status, Array.Empty<Diagnostic>());
      document.ImplementationIdToView![id] = existingView with { Status = status };
    }

    documentUpdates.OnNext(document);
  }

  private List<Diagnostic> GetDiagnosticsFromResult(Compilation document, VerificationResult result) {
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

  private void NotifyStatus(TextDocumentItem item, CompilationAfterTranslation document, CancellationToken cancellationToken) {
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

  public Task<CompilationAfterParsing> LastDocument => TranslatedDocument.ContinueWith(
    t => {
      if (t.IsCompletedSuccessfully) {
#pragma warning disable VSTHRD003
        return verificationCompleted.Task.ContinueWith(
          _ => Task.FromResult<CompilationAfterParsing>(t.Result), TaskScheduler.Current).Unwrap();
#pragma warning restore VSTHRD003
      }

      return ResolvedDocument;
    }, TaskScheduler.Current).Unwrap();
}
