using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Transactions;
using DafnyCore;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public static class BoogieOptionBag {
  public static readonly Option<IEnumerable<string>> BoogieFilter = new("--boogie-filter", @"
(experimental) Only check proofs whose Boogie name is matched by pattern <p>. This option may be specified multiple times to match multiple patterns. The pattern <p> may contain * wildcards which match any character zero or more times. If you are unsure of how Boogie names are generated, please pre- and postfix your pattern with a wildcard to enable matching on Dafny proof names."
    .TrimStart()) {
    ArgumentHelpName = "pattern",
  };

  public static readonly Option<IEnumerable<string>> BoogieArguments = new("--boogie",
    "Specify arguments that are passed to Boogie, a tool used to verify Dafny programs.") {
    ArgumentHelpName = "arguments",
    Arity = ArgumentArity.ZeroOrMore
  };

  public static readonly Option<uint> Cores = new("--cores", result => {

    var value = result.Tokens[^1].Value;
    if (value.EndsWith('%')) {
      if (double.TryParse(value.Substring(0, value.Length - 1), out var percentage)) {
        return Math.Max(1U, (uint)(percentage / 100.0 * Environment.ProcessorCount));
      }

      result.ErrorMessage = $"Could not parse percentage {value}";
      return 1;
    }

    if (uint.TryParse(value, out var number)) {
      if (number > 0) {
        return number;
      }

      result.ErrorMessage = $"Number of cores to use must be greater than 0";
      return 1;
    }
    result.ErrorMessage = $"Could not parse number {value}";
    return 1;
  }, true,
    "Run the Dafny verifier using <n> cores, or using <XX%> of the machine's logical cores.") {
    ArgumentHelpName = "count",
  };

  public static readonly Option<bool> NoVerify = new("--no-verify",
    "Skip verification") {
    ArgumentHelpName = "count"
  };

  public static readonly Option<uint> VerificationTimeLimit = new("--verification-time-limit",
    "Limit the number of seconds spent trying to verify each procedure") {
    ArgumentHelpName = "seconds",
  };

  public static readonly Option<int> VerificationErrorLimit =
    new("--error-limit", () => 5, "Set the maximum number of errors to report (0 for unlimited).");

  public static readonly Option<uint> SolverResourceLimit = new("--resource-limit",
    @"Specify the maximum resource limit (rlimit) value to pass to Z3. A resource limit is a deterministic
    alternative to a time limit. The output produced by `--log-format csv` includes the resource use of each proof
    effort, which you can use to determine an appropriate limit for your program. Multiplied by 1000 before
    sending to Z3.");
  public static readonly Option<string> SolverPlugin = new("--solver-plugin",
    @"Dafny uses Boogie as part of its verification process. This option allows customising that part using a Boogie plugin. More information about Boogie can be found at https://github.com/boogie-org/boogie. Information on how to construct Boogie plugins can be found by looking at the code in https://github.com/boogie-org/boogie/blob/v2.16.3/Source/Provers/SMTLib/ProverUtil.cs#L316");

  public static readonly Option<string> SolverLog =
    new("--solver-log", @"Specify a file to use to log the SMT-Lib text sent to the solver.") {
      IsHidden = true
    };

  public static readonly Option<bool> IsolateAssertions = new("--isolate-assertions", @"Verify each assertion in isolation.");

  public static readonly Option<FileInfo> SolverPath = new("--solver-path",
    "Can be used to specify a custom SMT solver to use for verifying Dafny proofs.") {
  };
  public static readonly Option<IList<string>> SolverOption = new("--solver-option",
    "Specify an option to control how the solver works.") {
  };


  static BoogieOptionBag() {
    Cores.SetDefaultValue((uint)((Environment.ProcessorCount + 1) / 2));

    DafnyOptions.RegisterLegacyBinding(BoogieFilter, (o, f) => o.ProcsToCheck.AddRange(f));
    DafnyOptions.RegisterLegacyBinding(BoogieArguments, (o, boogieOptions) => {
      var splitOptions = boogieOptions.SelectMany(SplitArguments).ToArray();
      if (splitOptions.Any()) {
        o.Parse(splitOptions.ToArray());
      }
    });
    DafnyOptions.RegisterLegacyBinding(Cores,
      (o, f) => o.VcsCores = f == 0 ? (1 + System.Environment.ProcessorCount) / 2 : (int)f);
    DafnyOptions.RegisterLegacyBinding(NoVerify, (o, f) => o.Verify = !f);
    DafnyOptions.RegisterLegacyBinding(VerificationTimeLimit, (o, f) => o.TimeLimit = f);
    DafnyOptions.RegisterLegacyBinding(SolverPath, (options, value) => {
      if (value != null) {
        options.ProverOptions.Add($"PROVER_PATH={value?.FullName}");
      }
    });
    DafnyOptions.RegisterLegacyBinding(SolverPlugin, (o, v) => {
      if (v is not null) {
        o.ProverDllName = v;
        o.TheProverFactory = ProverFactory.Load(o.ProverDllName);
      }
    });
    DafnyOptions.RegisterLegacyBinding(SolverResourceLimit, (o, v) => o.ResourceLimit = v);
    DafnyOptions.RegisterLegacyBinding(SolverLog, (o, v) => o.ProverLogFilePath = v);
    DafnyOptions.RegisterLegacyBinding(SolverOption, (o, v) => {
      if (v is not null) {
        o.ProverOptions.AddRange(v);
      }
    });
    DafnyOptions.RegisterLegacyBinding(VerificationErrorLimit, (options, value) => { options.ErrorLimit = value; });
    DafnyOptions.RegisterLegacyBinding(IsolateAssertions, (o, v) => o.VcsSplitOnEveryAssert = v);


    DooFile.RegisterLibraryChecks(
      new Dictionary<Option, DooFile.OptionCheck> {
        { BoogieArguments, DooFile.CheckOptionMatches },
        { BoogieFilter, DooFile.CheckOptionMatches },
        { NoVerify, DooFile.CheckOptionMatches },
      }
    );
    DooFile.RegisterNoChecksNeeded(
      Cores,
      VerificationTimeLimit,
      VerificationErrorLimit,
      IsolateAssertions,
      SolverLog,
      SolverOption,
      SolverPath,
      SolverPlugin,
      SolverResourceLimit
    );
  }

  private static IReadOnlyList<string> SplitArguments(string commandLine) {
    if (string.IsNullOrEmpty(commandLine)) {
      return Array.Empty<string>();
    }

    var inSingleQuote = false;
    var inDoubleQuote = false;
    var result = new List<string>();
    var start = 0;
    for (var end = 0; end < commandLine.Length; end++) {
      var store = false;
      if (commandLine[end] == '"' && !inSingleQuote) {
        store = inDoubleQuote;
        inDoubleQuote = !inDoubleQuote;
      }
      if (commandLine[end] == '\'' && !inDoubleQuote) {
        store = inSingleQuote;
        inSingleQuote = !inSingleQuote;
      }
      if (!inSingleQuote && !inDoubleQuote && commandLine[end] == ' ') {
        store = true;
      }

      if (store) {
        result.Add(commandLine.Substring(start, end - start));
        start = end + 1; // Skip the single or double quote or space in the next entry
      }
    }
    result.Add(commandLine.Substring(start, commandLine.Length - start));
    return result;
  }
}
