using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive;
using System.Reactive.Concurrency;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Util;
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
  IReadOnlyDictionary<Uri, DocumentVerificationTree> migratedVerificationTrees);

/// <summary>
/// The compilation of a single document version.
/// The document will be parsed, resolved, translated to Boogie and verified.
///
/// Compilation may be configured to pause after translation,
/// requiring a call to CompilationManager.Verify for the document to be verified.
///
/// Compilation is agnostic to document updates, it does not handle the migration of old document state.
/// </summary>
public class CompilationManager : IDisposable {

  private readonly ILogger logger;
  private readonly ITextDocumentLoader documentLoader;
  private readonly IProgramVerifier verifier;
  private readonly IGutterIconAndHoverVerificationDetailsManager gutterIconManager;

  // TODO CompilationManager shouldn't be aware of migration
  private readonly IReadOnlyDictionary<Uri, DocumentVerificationTree> migratedVerificationTrees;

  private TaskCompletionSource started = new();
  private readonly EventLoopScheduler verificationUpdateScheduler = new();
  private readonly CancellationTokenSource cancellationSource;

  private TaskCompletionSource verificationCompleted = new();
  private readonly DafnyOptions options;
  public Compilation StartingCompilation { get; }
  private readonly ExecutionEngine boogieEngine;

  private readonly Subject<Compilation> compilationUpdates = new();
  public IObservable<Compilation> CompilationUpdates => compilationUpdates;

  public Task<CompilationAfterParsing> ParsedCompilation { get; }
  public Task<CompilationAfterResolution> ResolvedCompilation { get; }

  public CompilationManager(
    ILogger<CompilationManager> logger,
    ITextDocumentLoader documentLoader,
    IProgramVerifier verifier,
    IGutterIconAndHoverVerificationDetailsManager gutterIconManager,
    DafnyOptions options,
    ExecutionEngine boogieEngine,
    Compilation compilation,
    IReadOnlyDictionary<Uri, DocumentVerificationTree> migratedVerificationTrees
    ) {
    this.options = options;
    StartingCompilation = compilation;
    this.boogieEngine = boogieEngine;
    this.migratedVerificationTrees = migratedVerificationTrees;

    this.documentLoader = documentLoader;
    this.logger = logger;
    this.verifier = verifier;
    this.gutterIconManager = gutterIconManager;
    cancellationSource = new();
    cancellationSource.Token.Register(() => started.TrySetCanceled(cancellationSource.Token));

    verificationTickets.Enqueue(Unit.Default);
    MarkVerificationFinished();

    ParsedCompilation = ParseAsync();
    ResolvedCompilation = ResolveAsync();
  }

  public void Start() {
    started.TrySetResult();
  }

  private async Task<CompilationAfterParsing> ParseAsync() {
    try {
      await started.Task;
      var parsedCompilation = await documentLoader.ParseAsync(options, StartingCompilation, migratedVerificationTrees,
        cancellationSource.Token);

      gutterIconManager.RecomputeVerificationTrees(parsedCompilation);
      foreach (var root in parsedCompilation.RootUris) {
        gutterIconManager.PublishGutterIcons(parsedCompilation, root, false);
      }

      compilationUpdates.OnNext(parsedCompilation);
      logger.LogDebug(
        $"Passed parsedCompilation to documentUpdates.OnNext, resolving ParsedCompilation task for version {parsedCompilation.Version}.");
      return parsedCompilation;

    } catch (OperationCanceledException) {
      throw;
    } catch (Exception e) {
      compilationUpdates.OnError(e);
      throw;
    }
  }

  private async Task<CompilationAfterResolution> ResolveAsync() {
    try {
      var parsedCompilation = await ParsedCompilation;
      var resolvedCompilation = await documentLoader.ResolveAsync(options, parsedCompilation, cancellationSource.Token);

      if (!resolvedCompilation.Program.Reporter.HasErrors) {
        gutterIconManager.RecomputeVerificationTrees(resolvedCompilation);
        foreach (var root in resolvedCompilation.RootUris) {
          gutterIconManager.PublishGutterIcons(resolvedCompilation, root, true);
        }
      }

      compilationUpdates.OnNext(resolvedCompilation);
      logger.LogDebug($"Passed resolvedCompilation to documentUpdates.OnNext, resolving ResolvedCompilation task for version {resolvedCompilation.Version}.");
      return resolvedCompilation;

    } catch (OperationCanceledException) {
      throw;
    } catch (Exception e) {
      compilationUpdates.OnError(e);
      throw;
    }
  }

  private static string GetImplementationName(Implementation implementation) {
    var prefix = implementation.Name.Split(BoogieGenerator.NameSeparator)[0];

    // Refining declarations get the token of what they're refining, so to distinguish them we need to
    // add the refining module name to the prefix.
    if (implementation.tok is RefinementToken refinementToken) {
      prefix += "." + refinementToken.InheritingModule.Name;
    }

    return prefix;
  }

  private int runningVerificationJobs;

  // When verifying a symbol, a ticket must be acquired before the SMT part of verification may start.
  private readonly AsyncQueue<Unit> verificationTickets = new();
  public async Task<bool> VerifySymbol(FilePosition verifiableLocation, bool onlyPrepareVerificationForGutterTests = false) {
    cancellationSource.Token.ThrowIfCancellationRequested();

    var compilation = await ResolvedCompilation;

    if (compilation.ResolutionDiagnostics.Values.SelectMany(x => x).Any(d =>
          d.Level == ErrorLevel.Error &&
          d.Source != MessageSource.Compiler &&
          d.Source != MessageSource.Verifier)) {
      throw new TaskCanceledException();
    }

    var verifiable = compilation.Program.FindNode(verifiableLocation.Uri, verifiableLocation.Position.ToDafnyPosition(),
      node => {
        if (node is not ICanVerify) {
          return false;
        }
        // Sometimes traversing the AST can return different versions of a single source AST node,
        // for example in the case of a LeastLemma, which is later also represented as a PrefixLemma.
        // This check ensures that we consistently use the same version of an AST node. 
        return compilation.Verifiables!.Contains(node);
      }) as ICanVerify;

    if (verifiable == null) {
      return false;
    }

    var containingModule = verifiable.ContainingModule;
    if (!containingModule.ShouldVerify(compilation.Program.Compilation)) {
      return false;
    }

    if (!onlyPrepareVerificationForGutterTests && !compilation.VerifyingOrVerifiedSymbols.TryAdd(verifiable, Unit.Default)) {
      return false;
    }
    compilationUpdates.OnNext(compilation);

    if (onlyPrepareVerificationForGutterTests) {
      await VerifyUnverifiedSymbol(onlyPrepareVerificationForGutterTests, verifiable, compilation);
      return true;
    }

    _ = VerifyUnverifiedSymbol(onlyPrepareVerificationForGutterTests, verifiable, compilation);
    return true;
  }

  private async Task VerifyUnverifiedSymbol(bool onlyPrepareVerificationForGutterTests, ICanVerify verifiable,
    CompilationAfterResolution compilation) {
    try {

      var ticket = verificationTickets.Dequeue(CancellationToken.None);
      var containingModule = verifiable.ContainingModule;

      IncrementJobs();

      IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>> tasksForModule;
      try {
        tasksForModule = await compilation.TranslatedModules.GetOrAdd(containingModule, async () => {
          var result = await verifier.GetVerificationTasksAsync(boogieEngine, compilation, containingModule,
            cancellationSource.Token);
          compilation.ResolutionDiagnostics =
            ((DiagnosticErrorReporter)compilation.Program.Reporter).AllDiagnosticsCopy;
          compilationUpdates.OnNext(compilation);
          foreach (var task in result) {
            cancellationSource.Token.Register(task.Cancel);
          }

          return result.GroupBy(t => ((IToken)t.Implementation.tok).GetFilePosition()).ToDictionary(
            g => g.Key,
            g => (IReadOnlyList<IImplementationTask>)g.ToList());
        });
      } catch (OperationCanceledException) {
        verificationCompleted.TrySetCanceled();
        throw;
      } catch (Exception e) {
        verificationCompleted.TrySetException(e);
        compilationUpdates.OnError(e);
        throw;
      }

      // For updated to be reliable, ImplementationsPerVerifiable must be Lazy
      var updated = false;
      var implementations = compilation.ImplementationsPerVerifiable.GetOrAdd(verifiable, () => {
        var tasksForVerifiable =
          tasksForModule.GetValueOrDefault(verifiable.NameToken.GetFilePosition()) ??
          new List<IImplementationTask>(0);

        updated = true;
        return tasksForVerifiable.ToDictionary(
          t => GetImplementationName(t.Implementation),
          t => new ImplementationView(t, PublishedVerificationStatus.Stale, Array.Empty<DafnyDiagnostic>()));
      });
      if (updated) {
        gutterIconManager.ReportImplementationsBeforeVerification(compilation,
          verifiable, implementations.Select(t => t.Value.Task.Implementation).ToArray());

        gutterIconManager.PublishGutterIcons(compilation, verifiable.Tok.Uri, true);
        compilationUpdates.OnNext(compilation);
      }

      // When multiple calls to VerifyUnverifiedSymbol are made, the order in which they pass this await matches the call order.
      await ticket;

      if (!onlyPrepareVerificationForGutterTests) {
        var tasks = implementations.Values.Select(t => t.Task).ToList();

        foreach (var task in tasks) {
          var statusUpdates = task.TryRun();
          if (statusUpdates == null) {
            if (task.CacheStatus is Completed completedCache) {
              foreach (var result in completedCache.Result.VCResults) {
                gutterIconManager.ReportVerifyImplementationRunning(compilation,
                  task.Implementation);
                gutterIconManager.ReportAssertionBatchResult(compilation,
                  new AssertionBatchResult(task.Implementation, result));
              }

              ReportVacuityAndRedundantAssumptionsChecks(compilation, task.Implementation, completedCache.Result);
              gutterIconManager.ReportEndVerifyImplementation(compilation, task.Implementation,
                completedCache.Result);
            }

            StatusUpdateHandlerFinally();
            return;
          }

          var incrementedJobs = Interlocked.Increment(ref runningVerificationJobs);
          logger.LogDebug(
            $"Incremented jobs for task, remaining jobs {incrementedJobs}, {compilation.Uri} version {compilation.Version}");

          statusUpdates.ObserveOn(verificationUpdateScheduler).Subscribe(
            update => {
              try {
                HandleStatusUpdate(compilation, verifiable, task, update);
              } catch (Exception e) {
                logger.LogError(e, "Caught exception in statusUpdates OnNext.");
              }
            },
            e => {
              if (e is not OperationCanceledException) {
                logger.LogError(e, $"Caught error in statusUpdates observable.");
              }

              StatusUpdateHandlerFinally();
            },
            StatusUpdateHandlerFinally
          );
        }

        void StatusUpdateHandlerFinally() {
          try {
            var remainingJobs = Interlocked.Decrement(ref runningVerificationJobs);
            logger.LogDebug(
              $"StatusUpdateHandlerFinally called, remaining jobs {remainingJobs}, {compilation.Uri} version {compilation.Version}, " +
              $"startingCompilation.version {StartingCompilation.Version}.");
            if (remainingJobs == 0) {
              FinishedNotifications(compilation, verifiable);
            }
          } catch (Exception e) {
            logger.LogCritical(e, "Caught exception while handling finally code of statusUpdates handler.");
          }
        }
      }

      DecrementJobs();
    }
    finally {
      verificationTickets.Enqueue(Unit.Default);
    }
  }

  public async Task Cancel(FilePosition filePosition) {
    var resolvedCompilation = await ResolvedCompilation;
    var canVerify = resolvedCompilation.Program.FindNode<ICanVerify>(filePosition.Uri, filePosition.Position.ToDafnyPosition());
    if (canVerify != null) {
      var implementations = resolvedCompilation.ImplementationsPerVerifiable.TryGetValue(canVerify, out var implementationsPerName)
        ? implementationsPerName!.Values : Enumerable.Empty<ImplementationView>();
      foreach (var view in implementations) {
        view.Task.Cancel();
      }
      resolvedCompilation.VerifyingOrVerifiedSymbols.TryRemove(canVerify, out _);
    }
  }

  public void IncrementJobs() {
    MarkVerificationStarted();
    var verifyTaskIncrementedJobs = Interlocked.Increment(ref runningVerificationJobs);
    logger.LogDebug($"Incremented jobs for verifyTask, remaining jobs {verifyTaskIncrementedJobs}, {StartingCompilation.Uri} version {StartingCompilation.Version}");
  }

  public void DecrementJobs() {
    var remainingJobs = Interlocked.Decrement(ref runningVerificationJobs);
    logger.LogDebug($"Decremented jobs, remaining jobs {remainingJobs}, {StartingCompilation.Uri} version {StartingCompilation.Version}");
    if (remainingJobs == 0) {
      logger.LogDebug($"Calling MarkVerificationFinished because there are no remaining verification jobs for {StartingCompilation.Uri}, version {StartingCompilation.Version}.");
      MarkVerificationFinished();
    }
  }

  private void FinishedNotifications(CompilationAfterResolution compilation, ICanVerify canVerify) {
    if (ReportGutterStatus) {
      if (!cancellationSource.IsCancellationRequested) {
        // All unvisited trees need to set them as "verified"
        gutterIconManager.SetAllUnvisitedMethodsAsVerified(compilation, canVerify);
      }

      gutterIconManager.PublishGutterIcons(compilation, canVerify.Tok.Uri, true);
    }

    MarkVerificationFinished();
  }

  private void HandleStatusUpdate(CompilationAfterResolution compilation, ICanVerify verifiable, IImplementationTask implementationTask, IVerificationStatus boogieStatus) {
    var status = StatusFromBoogieStatus(boogieStatus);

    var tokenString = implementationTask.Implementation.tok.TokenToString(options);
    var implementations = compilation.ImplementationsPerVerifiable[verifiable];

    var implementationName = GetImplementationName(implementationTask.Implementation);
    logger.LogDebug($"Received status {boogieStatus} for {tokenString}, version {compilation.Version}");
    if (boogieStatus is Running) {
      gutterIconManager.ReportVerifyImplementationRunning(compilation, implementationTask.Implementation);
    }

    DafnyDiagnostic[] newDiagnostics;
    if (boogieStatus is BatchCompleted batchCompleted) {
      gutterIconManager.ReportAssertionBatchResult(compilation,
        new AssertionBatchResult(implementationTask.Implementation, batchCompleted.VcResult));

      foreach (var counterExample in batchCompleted.VcResult.counterExamples) {
        compilation.Counterexamples.Add(counterExample);
      }

      newDiagnostics = GetDiagnosticsFromResult(compilation, implementationTask, batchCompleted.VcResult).ToArray();
    } else {
      newDiagnostics = Array.Empty<DafnyDiagnostic>();
    }

    var view = implementations.TryGetValue(implementationName, out var taskAndView)
      ? taskAndView
      : new ImplementationView(implementationTask, status, Array.Empty<DafnyDiagnostic>());
    implementations[implementationName] = view with { Status = status, Diagnostics = view.Diagnostics.Concat(newDiagnostics).ToArray() };

    if (boogieStatus is Completed completed) {
      var verificationResult = completed.Result;
      // Sometimes, the boogie status is set as Completed
      // but the assertion batches were not reported yet.
      // because they are on a different thread.
      // This loop will ensure that every vc result has been dealt with
      // before we report that the verification of the implementation is finished 
      foreach (var result in completed.Result.VCResults) {
        logger.LogDebug($"Possibly duplicate reporting assertion batch {result.vcNum} as completed in {tokenString}, version {compilation.Version}");
        gutterIconManager.ReportAssertionBatchResult(compilation,
          new AssertionBatchResult(implementationTask.Implementation, result));
      }
      ReportVacuityAndRedundantAssumptionsChecks(compilation, implementationTask.Implementation, verificationResult);
      gutterIconManager.ReportEndVerifyImplementation(compilation, implementationTask.Implementation, verificationResult);
    }
    compilationUpdates.OnNext(compilation);
  }

  private bool ReportGutterStatus => options.Get(GutterIconAndHoverVerificationDetailsManager.LineVerificationStatus);

  public static void ReportVacuityAndRedundantAssumptionsChecks(CompilationAfterResolution compilation,
    Implementation implementation, VerificationResult verificationResult) {
    var options = compilation.Program.Reporter.Options;
    if (!options.Get(CommonOptionBag.WarnContradictoryAssumptions)
        && !options.Get(CommonOptionBag.WarnRedundantAssumptions)
       ) {
      return;
    }

    ProofDependencyWarnings.WarnAboutSuspiciousDependenciesForImplementation(options, compilation.Program.Reporter,
      compilation.Program.ProofDependencyManager,
      new DafnyConsolePrinter.ImplementationLogEntry(implementation.VerboseName, implementation.tok),
      DafnyConsolePrinter.DistillVerificationResult(verificationResult));
    compilation.RefreshDiagnosticsFromProgramReporter();
  }

  private List<DafnyDiagnostic> GetDiagnosticsFromResult(CompilationAfterResolution compilation, IImplementationTask task, VCResult result) {
    var errorReporter = new DiagnosticErrorReporter(options, compilation.Uri.ToUri());
    var outcome = GetOutcome(result.outcome);
    foreach (var counterExample in result.counterExamples) {
      errorReporter.ReportBoogieError(counterExample.CreateErrorInformation(outcome, options.ForceBplErrors));
    }

    var implementation = task.Implementation;
    boogieEngine.ReportOutcome(null, outcome, outcomeError => errorReporter.ReportBoogieError(outcomeError),
      implementation.VerboseName, implementation.tok, null, TextWriter.Null,
      implementation.GetTimeLimit(options), result.counterExamples);

    var diagnostics = errorReporter.AllDiagnosticsCopy.Values.SelectMany(x => x);
    return diagnostics.OrderBy(d => d.Token.GetLspPosition()).ToList();
  }

  private ConditionGeneration.Outcome GetOutcome(ProverInterface.Outcome outcome) {
    switch (outcome) {
      case ProverInterface.Outcome.Valid:
        return ConditionGeneration.Outcome.Correct;
      case ProverInterface.Outcome.Invalid:
        return ConditionGeneration.Outcome.Errors;
      case ProverInterface.Outcome.TimeOut:
        return ConditionGeneration.Outcome.TimedOut;
      case ProverInterface.Outcome.OutOfMemory:
        return ConditionGeneration.Outcome.OutOfMemory;
      case ProverInterface.Outcome.OutOfResource:
        return ConditionGeneration.Outcome.OutOfResource;
      case ProverInterface.Outcome.Undetermined:
        return ConditionGeneration.Outcome.Inconclusive;
      case ProverInterface.Outcome.Bounded:
        return ConditionGeneration.Outcome.ReachedBound;
      default:
        throw new ArgumentOutOfRangeException(nameof(outcome), outcome, null);
    }
  }

  private static PublishedVerificationStatus StatusFromBoogieStatus(IVerificationStatus verificationStatus) {
    switch (verificationStatus) {
      case Stale:
        return PublishedVerificationStatus.Stale;
      case Queued:
        return PublishedVerificationStatus.Queued;
      case Running:
      case BatchCompleted:
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

  private void MarkVerificationStarted() {
    logger.LogDebug($"MarkVerificationStarted called for {StartingCompilation.Uri} version {StartingCompilation.Version}");
    if (verificationCompleted.Task.IsCompleted) {
      verificationCompleted = new TaskCompletionSource();
    }
  }

  private void MarkVerificationFinished() {
    logger.LogDebug($"MarkVerificationFinished called for {StartingCompilation.Uri} version {StartingCompilation.Version}");
    verificationCompleted.TrySetResult();
  }

  public Task<CompilationAfterParsing> LastDocument {
    get {
      logger.LogDebug($"LastDocument {StartingCompilation.Uri} will return document version {StartingCompilation.Version}");
      return ResolvedCompilation.ContinueWith(
        t => {
          if (t.IsCompletedSuccessfully) {
#pragma warning disable VSTHRD103
            return verificationCompleted.Task.ContinueWith(
              verificationCompletedTask => {
                logger.LogDebug(
                  $"LastDocument returning translated compilation {StartingCompilation.Uri} with status {verificationCompletedTask.Status}");
                return Task.FromResult<CompilationAfterParsing>(t.Result);
              }, TaskScheduler.Current).Unwrap();
#pragma warning restore VSTHRD103
          }

          return ParsedCompilation;
        }, TaskScheduler.Current).Unwrap();
    }
  }

  public async Task<TextEditContainer?> GetTextEditToFormatCode(Uri uri) {
    // TODO https://github.com/dafny-lang/dafny/issues/3416
    var parsedDocument = await ParsedCompilation;
    if (parsedDocument.GetDiagnostics(uri).Any(diagnostic =>
          diagnostic.Level == ErrorLevel.Error &&
          diagnostic.Source == MessageSource.Parser
        )) {
      return null;
    }

    var firstToken = parsedDocument.Program.GetFirstTokenForUri(uri);
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

  private bool disposed = false;
  public void Dispose() {
    if (disposed) {
      return;
    }

    disposed = true;
    CancelPendingUpdates();
    verificationUpdateScheduler.Dispose();
  }
}
