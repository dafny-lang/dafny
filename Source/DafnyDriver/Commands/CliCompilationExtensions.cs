using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Workspace;
using IToken = Microsoft.Dafny.IToken;

namespace DafnyDriver.Commands;

public static class CliCompilationExtensions {

  public static int ExitCode(this Compilation compilation) {
    var exitValue = compilation.Reporter.ErrorCount > 0 ? ExitValue.VERIFICATION_ERROR : ExitValue.SUCCESS;
    return (int)exitValue;
  }
  
  public static async Task VerifyAllAndPrintSummary(this Compilation compilation) {
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
              statSum.VerifiedCount += 1;
              break;
            case ProverInterface.Outcome.Invalid:
              statSum.ErrorCount += batchCompleted.VcResult.counterExamples.Count;
              break;
            case ProverInterface.Outcome.TimeOut:
              statSum.TimeoutCount += 1;
              break;
            case ProverInterface.Outcome.OutOfMemory:
              statSum.OutOfMemoryCount += 1;
              break;
            case ProverInterface.Outcome.OutOfResource:
              statSum.OutOfResourceCount += 1;
              break;
            case ProverInterface.Outcome.Undetermined:
              statSum.InconclusiveCount += 1;
              break;
            default:
              throw new ArgumentOutOfRangeException();
          }
        }
      }
    });
    
    var resolution = await compilation.Resolution;
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
        await compilation.VerifyCanVerify(canVerify, false);
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