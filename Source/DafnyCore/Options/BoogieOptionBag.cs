using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Transactions;
using DafnyCore;
using DafnyCore.Options;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public static class BoogieOptionBag {
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

  public static readonly Option<bool> NoVerify = new("--no-verify", "Skip verification");

  public static readonly Option<bool> HiddenNoVerify = new("--hidden-no-verify",
    "Allows building unverified libraries without recording that they were not verified.") {
    IsHidden = true
  };

  public static readonly Option<uint> VerificationTimeLimit = new("--verification-time-limit", () => 30,
    "Limit the number of seconds spent trying to verify each assertion batch. A value of 0 indicates no limit") {
    ArgumentHelpName = "seconds",
  };

  public static readonly Option<int> VerificationErrorLimit =
    new("--error-limit", () => 5, "Set the maximum number of errors to report (0 for unlimited).");

  public static readonly Option<uint> SolverResourceLimit = new("--resource-limit",
    result => {
      var value = result.Tokens[^1].Value;

      if (DafnyOptions.TryParseResourceCount(value, out var number)) {
        return number;
      }

      result.ErrorMessage = $"Cannot parse resource limit: {value}";
      return 0;
    },
    isDefault: false,
    @"Specify the maximum resource limit (rlimit) value to pass to Z3. A resource limit is a deterministic alternative to a time limit. The output produced by `--log-format csv` includes the resource use of each proof effort, which you can use to determine an appropriate limit for your program.");
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
    @"Specify an option to control how the solver works. Use --solver-option-help for details on possible parameters. Note that this directly changes the internal behavior of Boogie, and some option settings do not work well or at all with Dafny. More information about Boogie can be found at https://github.com/boogie-org/boogie.") {
    IsHidden = true
  };

  public static readonly Option<bool> SolverOptionHelp = new("--solver-option-help",
    @"Describe the possible parameters to --solver-option.") {
    IsHidden = true
  };


  static BoogieOptionBag() {
    Cores.SetDefaultValue((uint)((Environment.ProcessorCount + 1) / 2));

    DafnyOptions.RegisterLegacyBinding(BoogieArguments, (o, boogieOptions) => {
      var splitOptions = boogieOptions.SelectMany(SplitArguments).ToArray();
      if (splitOptions.Any()) {
        o.BaseParse(splitOptions.ToArray(), false);
      }
    });
    DafnyOptions.RegisterLegacyBinding(Cores,
      (o, f) => o.VcsCores = f == 0 ? (1 + System.Environment.ProcessorCount) / 2 : (int)f);
    DafnyOptions.RegisterLegacyBinding(NoVerify, (options, dotNotVerify) => {
      var shouldVerify = !dotNotVerify && !options.Get(HiddenNoVerify);
      options.Verify = shouldVerify; // Boogie won't verify
      options.DafnyVerify =
        shouldVerify ||
        options.Get(DeveloperOptionBag.BoogiePrint) != null ||
        options.Get(DeveloperOptionBag.SplitPrint) != null ||
        options.Get(DeveloperOptionBag.PassivePrint) != null;
    });
    DafnyOptions.RegisterLegacyBinding(VerificationTimeLimit, (o, f) => o.TimeLimit = f);

    DafnyOptions.RegisterLegacyBinding(SolverPath, (options, value) => {
      if (value != null) {
        options.ProverOptions.RemoveAll(s => s.StartsWith("PROVER_PATH="));
        options.ProverOptions.Add($"PROVER_PATH={value?.FullName}");
      }
    });
    SolverPlugin.AddValidator(r => {
      var fi = r.GetValueOrDefault<string>();
      if (!File.Exists(fi)) {
        r.ErrorMessage = $"--solver-plugin: File {fi} does not exist";
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
    DafnyOptions.RegisterLegacyBinding(SolverOptionHelp, (o, v) => o.ProverHelpRequested = v);
    DafnyOptions.RegisterLegacyBinding(VerificationErrorLimit, (options, value) => { options.ErrorLimit = value; });
    DafnyOptions.RegisterLegacyBinding(IsolateAssertions, (o, v) => o.VcsSplitOnEveryAssert = v);

    OptionRegistry.RegisterGlobalOption(BoogieArguments, OptionCompatibility.CheckOptionMatches);
    OptionRegistry.RegisterGlobalOption(NoVerify, OptionCompatibility.OptionLibraryImpliesLocalError);
    OptionRegistry.RegisterOption(HiddenNoVerify, OptionScope.Cli);
    OptionRegistry.RegisterOption(Cores, OptionScope.Cli);
    OptionRegistry.RegisterOption(VerificationTimeLimit, OptionScope.Cli);
    OptionRegistry.RegisterOption(VerificationErrorLimit, OptionScope.Cli);
    OptionRegistry.RegisterOption(IsolateAssertions, OptionScope.Cli);
    OptionRegistry.RegisterOption(SolverLog, OptionScope.Cli);
    OptionRegistry.RegisterOption(SolverOption, OptionScope.Cli);
    OptionRegistry.RegisterOption(SolverOptionHelp, OptionScope.Cli);
    OptionRegistry.RegisterOption(SolverPath, OptionScope.Cli);
    OptionRegistry.RegisterOption(SolverPlugin, OptionScope.Cli);
    OptionRegistry.RegisterOption(SolverResourceLimit, OptionScope.Cli);
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
