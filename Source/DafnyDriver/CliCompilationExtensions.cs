using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Workspace;
using IToken = Microsoft.Dafny.IToken;

namespace DafnyDriver.Commands;

public static class CliCompilationExtensions {

  public static int ExitCode(this Compilation compilation) {
    ExitValue exitValue;
    if (compilation.Reporter.HasErrorsUntilResolver) {
      exitValue = ExitValue.DAFNY_ERROR;
    } else if (compilation.Reporter.ErrorCount > 0) {
      exitValue = ExitValue.VERIFICATION_ERROR;
    } else {
      exitValue = ExitValue.SUCCESS;
    }

    return (int)exitValue;
  }

  public static async Task VerifyAllAndPrintSummary(this Compilation compilation) {
    var resolution = await compilation.Resolution;
    if (resolution.ResolvedProgram.Reporter.HasErrorsUntilResolver) {
      return;
    }

    var options = compilation.Input.Options;
    var statSum = new PipelineStatistics();
    var canVerifyResults = new Dictionary<IToken, CanVerifyResults>();
    compilation.Updates.Subscribe(ev => {

      if (ev is CanVerifyPartsIdentified canVerifyPartsIdentified) {
        var canVerifyResult = canVerifyResults[canVerifyPartsIdentified.CanVerify.Tok];
        foreach (var part in canVerifyPartsIdentified.Parts) {
          canVerifyResult.Tasks.Add(part);
        }
        if (canVerifyResult.CompletedParts.Count == canVerifyResult.Tasks.Count) {
          canVerifyResult.Finished.SetResult();
        }
      }

      if (ev is BoogieUpdate boogieUpdate) {
        if (boogieUpdate.BoogieStatus is Completed completed) {
          var canVerifyResult = canVerifyResults[BoogieGenerator.ToDafnyToken(false, boogieUpdate.ImplementationTask.Implementation.tok)];
          canVerifyResult.CompletedParts.Add((boogieUpdate.ImplementationTask, completed));
          if (canVerifyResult.CompletedParts.Count == canVerifyResult.Tasks.Count) {
            canVerifyResult.Finished.SetResult();
          }
        }
        if (boogieUpdate.BoogieStatus is BatchCompleted batchCompleted) {
          switch (batchCompleted.VcResult.outcome) {
            case ProverInterface.Outcome.Valid:
            case ProverInterface.Outcome.Bounded:
              Interlocked.Increment(ref statSum.VerifiedCount);
              break;
            case ProverInterface.Outcome.Invalid:
              Interlocked.Add(ref statSum.ErrorCount, batchCompleted.VcResult.counterExamples.Count);
              break;
            case ProverInterface.Outcome.TimeOut:
              Interlocked.Increment(ref statSum.TimeoutCount);
              break;
            case ProverInterface.Outcome.OutOfMemory:
              Interlocked.Increment(ref statSum.OutOfMemoryCount);
              break;
            case ProverInterface.Outcome.OutOfResource:
              Interlocked.Increment(ref statSum.OutOfResourceCount);
              break;
            case ProverInterface.Outcome.Undetermined:
              Interlocked.Increment(ref statSum.InconclusiveCount);
              break;
            default:
              throw new ArgumentOutOfRangeException();
          }
        }
      }
    });

    var canVerifies = resolution.CanVerifies?.ToList();

    if (canVerifies != null) {
      var orderedCanVerifies = canVerifies.OrderBy(v => v.Tok.pos).ToList();
      foreach (var canVerify in orderedCanVerifies) {
        canVerifyResults[canVerify.Tok] = new CanVerifyResults();
        await compilation.VerifyCanVerify(canVerify, false);
      }

      foreach (var canVerify in orderedCanVerifies) {
        var results = canVerifyResults[canVerify.Tok];
        await results.Finished.Task;
        foreach (var (task, completed) in results.CompletedParts) {
          foreach (var vcResult in completed.Result.VCResults) {
            Compilation.ReportDiagnosticsInResult(options, task, vcResult, compilation.Reporter);
          }
        }
      }
    }
    LegacyCliCompilation.WriteTrailer(options, /* TODO ErrorWriter? */ options.OutputWriter, statSum);
  }
}

struct CanVerifyResults {
  public readonly TaskCompletionSource Finished = new();
  public readonly List<(IImplementationTask, Completed)> CompletedParts = new();
  public readonly HashSet<IImplementationTask> Tasks = new();

  public CanVerifyResults() {
  }
}