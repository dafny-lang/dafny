using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using DafnyCore;
using Microsoft.Boogie;

// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
namespace Microsoft.Dafny;

public class GenerateTestsCommand : ICommandSpec {
  public IEnumerable<Option> Options =>
    new Option[] {
      LoopUnroll,
      SequenceLengthLimit,
      BoogieOptionBag.SolverLog,
      BoogieOptionBag.SolverOption,
      BoogieOptionBag.SolverOptionHelp,
      BoogieOptionBag.SolverPath,
      BoogieOptionBag.SolverPlugin,
      BoogieOptionBag.SolverResourceLimit,
      BoogieOptionBag.VerificationTimeLimit,
      PrintBpl,
      CoverageReport,
      ForcePrune
    }.Concat(ICommandSpec.ConsoleOutputOptions).
      Concat(ICommandSpec.ResolverOptions);

  private enum Mode {
    Path,
    Block,
    InlinedBlock
  }

  /// <summary>
  /// Return a copy of the given DafnyOption instance that (for the purposes
  /// of test generation) is identical to the <param name="options"></param>
  /// parameter in everything except the value of the ProcsToCheck field that
  /// determines the procedures to be verified and should be set to the value of
  /// the <param name="proceduresToVerify"></param> parameter.
  /// </summary>
  internal static DafnyOptions CopyForProcedure(DafnyOptions options, HashSet<string> proceduresToVerify) {
    var copy = new DafnyOptions(options);
    copy.ProcsToCheck = proceduresToVerify.ToList();
    return copy;
  }

  private readonly Argument<Mode> modeArgument = new("mode", @"
Block - Generate tests targeting block-coverage.
InlinedBlock - Generate tests targeting block coverage after inlining (call-graph sensitive block coverage).
Path - Generate tests targeting path-coverage.");

  public Command Create() {
    var result = new Command("generate-tests", "(Experimental) Generate Dafny tests that ensure block or path coverage of a particular Dafny program.");
    result.AddArgument(modeArgument);
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    var mode = context.ParseResult.GetValueForArgument(modeArgument) switch {
      Mode.Path => TestGenerationOptions.Modes.Path,
      Mode.Block => TestGenerationOptions.Modes.Block,
      Mode.InlinedBlock => TestGenerationOptions.Modes.InlinedBlock,
      _ => throw new ArgumentOutOfRangeException()
    };
    PostProcess(dafnyOptions, options, context, mode);
  }

  internal static void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context, TestGenerationOptions.Modes mode) {
    dafnyOptions.CompilerName = "cs";
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = false;
    dafnyOptions.ForceCompile = false;
    dafnyOptions.DeprecationNoise = 0;
    dafnyOptions.ForbidNondeterminism = true;
    dafnyOptions.DefiniteAssignmentLevel = 2;
    dafnyOptions.UseBaseNameForFileName = false;
    dafnyOptions.VerifyAllModules = true;
    dafnyOptions.TypeEncodingMethod = CoreOptions.TypeEncoding.Predicates;
    dafnyOptions.Set(DafnyConsolePrinter.ShowSnippets, false);
    dafnyOptions.TestGenOptions.Mode = mode;
  }

  public static readonly Option<uint> SequenceLengthLimit = new("--length-limit",
    "Add an axiom that sets the length of all sequences to be no greater than <n>. 0 (default) indicates no limit.") {
  };
  public static readonly Option<int> LoopUnroll = new("--loop-unroll", () => -1,
    "Higher values can improve accuracy of the analysis at the cost of taking longer to run.") {
  };
  public static readonly Option<string> PrintBpl = new("--print-bpl",
    "Print the Boogie code used during test generation.") {
    ArgumentHelpName = "filename"
  };
  public static readonly Option<string> CoverageReport = new("--coverage-report",
    "Emit expected test coverage report to a given directory.") {
    ArgumentHelpName = "directory"
  };
  public static readonly Option<bool> ForcePrune = new("--force-prune",
    "Enable axiom pruning that Dafny uses to speed up verification. This may negatively affect the quality of tests.") {
  };
  static GenerateTestsCommand() {
    DafnyOptions.RegisterLegacyBinding(LoopUnroll, (options, value) => {
      options.LoopUnrollCount = value;
    });
    DafnyOptions.RegisterLegacyBinding(SequenceLengthLimit, (options, value) => {
      options.TestGenOptions.SeqLengthLimit = value;
    });
    DafnyOptions.RegisterLegacyBinding(PrintBpl, (options, value) => {
      options.TestGenOptions.PrintBpl = value;
    });
    DafnyOptions.RegisterLegacyBinding(CoverageReport, (options, value) => {
      options.TestGenOptions.CoverageReport = value;
    });
    DafnyOptions.RegisterLegacyBinding(ForcePrune, (options, value) => {
      options.TestGenOptions.ForcePrune = value;
    });

    DooFile.RegisterNoChecksNeeded(
      LoopUnroll,
      SequenceLengthLimit,
      PrintBpl,
      CoverageReport,
      ForcePrune
    );
  }
}
