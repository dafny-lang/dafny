using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using DafnyCore;

namespace Microsoft.Dafny;

static class MeasureComplexityCommand {
  public static IEnumerable<Option> Options => new Option[] {
    Iterations,
    RandomSeed,
  }.Concat(DafnyCommands.VerificationOptions).
    Concat(DafnyCommands.ResolverOptions);

  static MeasureComplexityCommand() {
    DafnyOptions.RegisterLegacyBinding(Iterations, (o, v) => o.RandomizeVcIterations = (int)v);
    DafnyOptions.RegisterLegacyBinding(RandomSeed, (o, v) => o.RandomSeed = (int)v);

    DooFile.RegisterNoChecksNeeded(
      Iterations,
      RandomSeed
    );
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
    DafnyCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => {
      options.Compile = false;
      return CompilerDriver.RunCompiler(options);
    });
    return result;
  }
}
