using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using DafnyCore;

namespace Microsoft.Dafny;

public class GenerateTestsCommand : ICommandSpec {
  public IEnumerable<Option> Options =>
    new Option[] {
      // IMPORTANT: Before adding new options, make sure they are
      // appropriately copied over in the CopyForProcedure method below
      LoopUnroll,
      SequenceLengthLimit,
      Target,
      BoogieOptionBag.SolverLog,
      BoogieOptionBag.SolverOption,
      BoogieOptionBag.SolverOptionHelp,
      BoogieOptionBag.SolverPath,
      BoogieOptionBag.SolverPlugin,
      BoogieOptionBag.SolverResourceLimit,
      BoogieOptionBag.VerificationTimeLimit,
      PrintBpl,
      DisablePrune
    }.Concat(ICommandSpec.ConsoleOutputOptions).
      Concat(ICommandSpec.ResolverOptions);

  private enum Mode {
    Path,
    Block
  }

  /// <summary>
  /// Return a copy of the given DafnyOption instance that (for the purposes
  /// of test generation) is identical to the <param name="options"></param>
  /// parameter in everything except the value of the ProcsToCheck field that
  /// determines the procedures to be verified and should be set to the value of
  /// the <param name="procedureToVerify"></param> parameter.
  /// </summary>
  internal static DafnyOptions CopyForProcedure(DafnyOptions options, string procedureToVerify) {
    var copy = new DafnyOptions(options);
    copy.ProcsToCheck = new List<string>() { procedureToVerify };
    return copy;
  }

  private readonly Argument<Mode> modeArgument = new("mode", @"
block - Prints block-coverage tests for the given program.
path - Prints path-coverage tests for the given program.");

  public Command Create() {
    var result = new Command("generate-tests", "(Experimental) Generate Dafny tests that ensure block or path coverage of a particular Dafny program.");
    result.AddArgument(modeArgument);
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    // IMPORTANT: Before adding new default options, make sure they are
    // appropriately copied over in the CopyForProcedure method above
    dafnyOptions.CompilerName = "cs";
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = false;
    dafnyOptions.ForceCompile = false;
    dafnyOptions.DeprecationNoise = 0;
    dafnyOptions.ForbidNondeterminism = true;
    dafnyOptions.DefiniteAssignmentLevel = 2;
    dafnyOptions.Set(DafnyConsolePrinter.ShowSnippets, false);

    var mode = context.ParseResult.GetValueForArgument(modeArgument);
    dafnyOptions.TestGenOptions.Mode = mode switch {
      Mode.Path => TestGenerationOptions.Modes.Path,
      Mode.Block => TestGenerationOptions.Modes.Block,
      _ => throw new ArgumentOutOfRangeException()
    };
  }

  public static readonly Option<string> Target = new("--target-method",
    "If specified, only this method will be tested.") {
    ArgumentHelpName = "name"
  };
  public static readonly Option<uint> SequenceLengthLimit = new("--length-limit",
    "Add an axiom that sets the length of all sequences to be no greater than <n>. 0 (default) indicates no limit.") {
  };
  public static readonly Option<int> LoopUnroll = new("--loop-unroll",
    "Higher values can improve accuracy of the analysis at the cost of taking longer to run.") {
  };
  public static readonly Option<string> PrintBpl = new("--print-bpl",
    "Print the Boogie code used during test generation.") {
    ArgumentHelpName = "filename"
  };
  public static readonly Option<bool> DisablePrune = new("--no-prune",
    "Disable axiom pruning that Dafny uses to speed up verification.") {
  };
  static GenerateTestsCommand() {
    DafnyOptions.RegisterLegacyBinding(LoopUnroll, (options, value) => {
      options.LoopUnrollCount = value;
    });
    DafnyOptions.RegisterLegacyBinding(SequenceLengthLimit, (options, value) => {
      options.TestGenOptions.SeqLengthLimit = value;
    });
    DafnyOptions.RegisterLegacyBinding(Target, (options, value) => {
      options.TestGenOptions.TargetMethod = value;
    });
    DafnyOptions.RegisterLegacyBinding(PrintBpl, (options, value) => {
      options.TestGenOptions.PrintBpl = value;
    });
    DafnyOptions.RegisterLegacyBinding(DisablePrune, (options, value) => {
      options.TestGenOptions.DisablePrune = value;
    });

    DooFile.RegisterNoChecksNeeded(
      LoopUnroll,
      SequenceLengthLimit,
      Target,
      PrintBpl,
      DisablePrune
    );
  }
}
