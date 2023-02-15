using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

public class MeasureComplexityCommand : ICommandSpec {
  public IEnumerable<Option> Options => new Option[] {
    Iterations,
    RandomSeed,
    Format,
    IsolateAssertions,
  }.Concat(ICommandSpec.VerificationOptions).
    Concat(ICommandSpec.ResolverOptions);

  static MeasureComplexityCommand() {
    DafnyOptions.RegisterLegacyBinding(Iterations, (o, v) => o.RandomSeedIterations = (int)v);
    DafnyOptions.RegisterLegacyBinding(RandomSeed, (o, v) => o.RandomSeed = (int)v);
    DafnyOptions.RegisterLegacyBinding(IsolateAssertions, (o, v) => o.VcsSplitOnEveryAssert = v);
    DafnyOptions.RegisterLegacyBinding(Format, (o, v) => o.VerificationLoggerConfigs = v);
  }

  private static readonly Option<uint> RandomSeed = new("--random-seed", () => 0U,
    $"Turn on randomization of the input that Dafny passes to the SMT solver and turn on randomization in the SMT solver itself. Certain Dafny proofs are complex in the sense that changes to the proof that preserve its meaning may cause its verification result to change. This option simulates meaning-preserving changes to the proofs without requiring the user to actually make those changes. The proof changes are renaming variables and reordering declarations in the SMT input passed to the solver, and setting solver options that have similar effects.");

  private static readonly Option<uint> Iterations = new("--iterations", () => 10U,
    $"Attempt to verify each proof n times with n random seeds, each seed derived from the previous one. {RandomSeed.Name} can be used to specify the first seed, which will otherwise be 0.") {
    ArgumentHelpName = "n"
  };

  private static readonly Option<bool> IsolateAssertions = new("--isolate-assertions", @"Verify each assertion in isolation.");

  private static readonly Option<List<string>> Format = new("--format", $@"
Logs verification results using the given test result format. The currently supported formats are `trx`, `csv`, and `text`. These are: the XML-based format commonly used for test results for .NET languages, a custom CSV schema, and a textual format meant for human consumption. You can provide configuration using the same string format as when using the --logger option for dotnet test, such as: --format ""trx;LogFileName=<...>"");
  
The `trx` and `csv` formats automatically choose an output file name by default, and print the name of this file to the console. The `text` format prints its output to the console by default, but can send output to a file given the `LogFileName` option.

The `text` format also includes a more detailed breakdown of what assertions appear in each assertion batch. When combined with the {IsolateAssertions.Name} option, it will provide approximate time and resource use costs for each assertion, allowing identification of especially expensive assertions.".TrimStart()) {
    ArgumentHelpName = "configuration"
  };

  public Command Create() {
    var result = new Command("measure-complexity", "(Experimental) Measure the complexity of verifying the program.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
  }
}
