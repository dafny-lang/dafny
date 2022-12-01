using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class ProofComplexityCommand : ICommandSpec {
  public IEnumerable<IOptionSpec> Options => new IOptionSpec[] {
    IterationsOption.Instance,
    RandomSeedOption.Instance,
    FormatOption.Instance,
    IsolateAssertionsOption.Instance,
  }.Concat(ICommandSpec.VerificationOptions).
    Concat(ICommandSpec.CommonOptions);

  public Command Create() {
    var result = new Command("check-proof-complexity", "(experimental) Check the complexity of the program proofs. Be aware that the name, options and output of this command will change in the future.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
  }
}

class IsolateAssertionsOption : BooleanOption {
  public static readonly IsolateAssertionsOption Instance = new();
  public override string LongName => "isolate-assertions";

  public override string Description => @"Verify each assertion in isolation.";

  public override string PostProcess(DafnyOptions options) {
    options.VcsSplitOnEveryAssert = Get(options);
    return null;
  }
}

class FormatOption : CommandLineOption<IEnumerable<string>> {
  public static readonly FormatOption Instance = new();
  public override object DefaultValue => Enumerable.Empty<string>();

  public override string LongName => "format";
  public override string ArgumentName => "configuration";

  public override string Description => $@"
Logs verification results using the given test result format. The currently supported formats are `trx`, `csv`, and `text`. These are: the XML-based format commonly used for test results for .NET languages, a custom CSV schema, and a textual format meant for human consumption. You can provide configuration using the same string format as when using the --logger option for dotnet test, such as: --format ""trx;LogFileName=<...>.z""
  
The `trx` and `csv` formats automatically choose an output file name by default, and print the name of this file to the console. The `text` format prints its output to the console by default, but can send output to a file given the `LogFileName` option.

The `text` format also includes a more detailed breakdown of what assertions appear in each assertion batch. When combined with the {IsolateAssertionsOption.Instance.LongName}git d option, it will provide approximate time and resource use costs for each assertion, allowing identification of especially expensive assertions.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.VerificationLoggerConfigs = Get(options).ToList();
    return null;
  }

  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    throw new System.NotImplementedException();
  }
}

class RandomSeedOption : NaturalNumberOption {
  public static readonly RandomSeedOption Instance = new();
  public override object DefaultValue => 0U;
  public override string LongName => "random-seed";
  public override string ArgumentName => "seed";

  public override string Description =>
    $"Turn on randomization of the input that Dafny passes to the SMT solver and turn on randomization in the SMT solver itself. Certain Dafny proofs are complex in the sense that changes to the proof that preserve its meaning may cause its verification result to change. This option simulates meaning-preserving changes to the proofs without requiring the user to actually make those changes. The proof changes are renaming variables and reordering declarations in the SMT input passed to the solver, and setting solver options that have similar effects.";

  public override string PostProcess(DafnyOptions options) {
    if (Get(options) != (uint)DefaultValue) {
      options.RandomSeed = (int?)Get(options);
    }

    return null;
  }
}

class IterationsOption : NaturalNumberOption {
  public static readonly IterationsOption Instance = new();
  public override object DefaultValue => 10U;
  public override string LongName => "iterations";
  public override string ArgumentName => "n";

  public override string Description =>
    $"Attempt to verify each proof n times with n random seeds, each seed derived from the previous one.  {RandomSeedOption.Instance.LongName} can be used to specify the first seed, which will otherwise be 0.";

  public override string PostProcess(DafnyOptions options) {
    options.RandomSeedIterations = (int)Get(options);
    return null;
  }
}
