using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using System.Reactive.Subjects;
using System.Threading.Tasks;
using DafnyCore;
using DafnyDriver.Commands;

namespace Microsoft.Dafny;

static class MeasureComplexityCommand {
  public static IEnumerable<Option> Options => new Option[] {
    Iterations,
    RandomSeed,
    VerifyCommand.FilterSymbol,
    VerifyCommand.FilterPosition,
  }.Concat(DafnyCommands.VerificationOptions).
    Concat(DafnyCommands.ResolverOptions);

  static MeasureComplexityCommand() {
    DafnyOptions.RegisterLegacyBinding(Iterations, (o, v) => o.RandomizeVcIterations = (int)v);
    DafnyOptions.RegisterLegacyBinding(RandomSeed, (o, v) => o.RandomSeed = (int)v);

    DooFile.RegisterNoChecksNeeded(Iterations, false);
    DooFile.RegisterNoChecksNeeded(RandomSeed, false);
  }

  private static readonly Option<uint> RandomSeed = new("--random-seed", () => 0U,
    $"Turn on randomization of the input that Dafny passes to the SMT solver and turn on randomization in the SMT solver itself. Certain Dafny proofs are complex in the sense that changes to the proof that preserve its meaning may cause its verification result to change. This option simulates meaning-preserving changes to the proofs without requiring the user to actually make those changes. The proof changes are renaming variables and reordering declarations in the SMT input passed to the solver, and setting solver options that have similar effects.");

  private static readonly Option<uint> Iterations = new("--iterations", () => 10U,
    $"Attempt to verify each proof n times with n random seeds, each seed derived from the previous one. {RandomSeed.Name} can be used to specify the first seed, which will otherwise be 0.") {
    ArgumentHelpName = "n"
  };

  public static Command Create() {
    var result = new Command("measure-complexity", "(Experimental) Measure the complexity of verifying the program.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => Execute(options));
    return result;
  }

  private static async Task<int> Execute(DafnyOptions options) {
    if (options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
      options.TrackVerificationCoverage = true;
    }

    var compilation = CliCompilation.Create(options);
    compilation.Start();

    var resolution = await compilation.Resolution;
    if (resolution != null) {
      Subject<CanVerifyResult> verificationResults = new();

      // We should redesign the output of this command 
      // It should start out with a summary that reports how many proofs are brittle, and shows statistical data,
      // such as averages and standard-deviations.
      // For error diagnostics, we should group duplicates and say how often they occur.
      // Performance data of individual verification tasks (VCs) should be grouped by VcNum (the assertion batch).

      var summaryReported = VerifyCommand.ReportVerificationSummary(compilation, verificationResults);
      var proofDependenciesReported = VerifyCommand.ReportProofDependencies(compilation, resolution, verificationResults);
      var verificationResultsLogged = VerifyCommand.LogVerificationResults(compilation, resolution, verificationResults);

      await RunVerificationIterations(options, compilation, verificationResults);
      await summaryReported;
      await verificationResultsLogged;
      await proofDependenciesReported;
    }

    return await compilation.GetAndReportExitCode();
  }

  private static async Task RunVerificationIterations(DafnyOptions options, CliCompilation compilation,
    IObserver<CanVerifyResult> verificationResultsObserver) {
    int iterationSeed = (int)options.Get(RandomSeed);
    var random = new Random(iterationSeed);
    foreach (var iteration in Enumerable.Range(0, (int)options.Get(Iterations))) {
      await options.OutputWriter.WriteLineAsync(
        $"Starting verification of iteration {iteration} with seed {iterationSeed}");
      try {
        await foreach (var result in compilation.VerifyAllLazily(iterationSeed)) {
          verificationResultsObserver.OnNext(result);
        }
      } catch (Exception e) {
        verificationResultsObserver.OnError(e);
      }
      iterationSeed = random.Next();
    }
    verificationResultsObserver.OnCompleted();
  }
}
