using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using VC;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record BoogieUpdate(ICanVerify CanVerify, IImplementationTask ImplementationTask, IVerificationStatus BoogieStatus)
  : ICompilationEvent {
  public Task<IdeState> UpdateState(DafnyOptions options, ILogger logger, IProjectDatabase projectDatabase,
    IdeState previousState) {
    UpdateGutterIconTrees(options, logger, previousState);

    var name = Compilation.GetImplementationName(ImplementationTask.Implementation);
    var status = StatusFromBoogieStatus(BoogieStatus);
    var uri = CanVerify.Tok.Uri;
    var range = CanVerify.NameToken.GetLspRange();

    var previousVerificationResult = previousState.VerificationResults[uri][range];
    var previousImplementations = previousVerificationResult.Implementations;
    var previousView = previousImplementations.GetValueOrDefault(name) ?? new IdeImplementationView(range, status, Array.Empty<Diagnostic>(), false);
    var counterExamples = previousState.Counterexamples;
    bool hitErrorLimit = previousView.HitErrorLimit;
    var diagnostics = previousView.Diagnostics;
    if (BoogieStatus is Running) {
      diagnostics = Array.Empty<Diagnostic>();
      hitErrorLimit = false;
    }

    if (BoogieStatus is BatchCompleted batchCompleted) {
      counterExamples = counterExamples.Concat(batchCompleted.VcResult.counterExamples);
      hitErrorLimit |= batchCompleted.VcResult.maxCounterExamples == batchCompleted.VcResult.counterExamples.Count;
      var newDiagnostics = GetDiagnosticsFromResult(options, previousState, ImplementationTask, batchCompleted.VcResult).ToArray();
      diagnostics = diagnostics.Concat(newDiagnostics.Select(d => d.ToLspDiagnostic())).ToList();
      logger.LogTrace($"BatchCompleted received for {previousState.Input} and found #{newDiagnostics.Length} new diagnostics.");
    }
    var view = new IdeImplementationView(range, status, diagnostics.ToList(), previousView.HitErrorLimit || hitErrorLimit);
    return Task.FromResult(previousState with {
      Counterexamples = counterExamples,
      VerificationResults = previousState.VerificationResults.SetItem(uri, previousState.VerificationResults[uri].SetItem(range, previousVerificationResult with {
        Implementations = previousVerificationResult.Implementations.SetItem(name, view)
      }))
    });
  }

  private void UpdateGutterIconTrees(DafnyOptions options, ILogger logger, IdeState previousState) {
    var gutterIconManager = new GutterIconAndHoverVerificationDetailsManager(logger);
    if (BoogieStatus is Running) {
      gutterIconManager.ReportVerifyImplementationRunning(previousState, ImplementationTask.Implementation);
    }

    if (BoogieStatus is BatchCompleted batchCompleted) {
      gutterIconManager.ReportAssertionBatchResult(previousState,
        new AssertionBatchResult(ImplementationTask.Implementation, batchCompleted.VcResult));
    }

    if (BoogieStatus is Completed completed) {
      var tokenString = BoogieGenerator.ToDafnyToken(true, ImplementationTask.Implementation.tok).TokenToString(options);
      var verificationResult = completed.Result;
      // Sometimes, the boogie status is set as Completed
      // but the assertion batches were not reported yet.
      // because they are on a different thread.
      // This loop will ensure that every vc result has been dealt with
      // before we report that the verification of the implementation is finished 
      foreach (var result in completed.Result.VCResults) {
        logger.LogDebug(
          $"Possibly duplicate reporting assertion batch {result.vcNum} as completed in {tokenString}, version {previousState.Version}");
        gutterIconManager.ReportAssertionBatchResult(previousState,
          new AssertionBatchResult(ImplementationTask.Implementation, result));
      }

      gutterIconManager.ReportEndVerifyImplementation(previousState, ImplementationTask.Implementation, verificationResult);
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

  private List<DafnyDiagnostic> GetDiagnosticsFromResult(DafnyOptions options, IdeState state, IImplementationTask task, VCResult result) {
    var errorReporter = new ObservableErrorReporter(options, state.Uri);
    List<DafnyDiagnostic> diagnostics = new();
    errorReporter.Updates.Subscribe(d => diagnostics.Add(d.Diagnostic));
    var outcome = GetOutcome(result.outcome);
    foreach (var counterExample in result.counterExamples) {
      errorReporter.ReportBoogieError(counterExample.CreateErrorInformation(outcome, options.ForceBplErrors));
    }

    var implementation = task.Implementation;

    // The Boogie API forces us to create a temporary engine here to report the outcome, even though it only uses the options.
    var boogieEngine = new ExecutionEngine(options, new VerificationResultCache(),
      CustomStackSizePoolTaskScheduler.Create(0, 0));
    boogieEngine.ReportOutcome(null, outcome, outcomeError => errorReporter.ReportBoogieError(outcomeError, false),
      implementation.VerboseName, implementation.tok, null, TextWriter.Null,
      implementation.GetTimeLimit(options), result.counterExamples);

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
}