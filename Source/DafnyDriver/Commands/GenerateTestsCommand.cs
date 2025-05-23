using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using DafnyCore;
using DafnyTestGeneration;
using Microsoft.Boogie;

// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
namespace Microsoft.Dafny;

static class GenerateTestsCommand {
  public static IEnumerable<Option> Options {
    get {
      return new Option[] {
        IgnoreWarnings,
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
        ExpectedCoverageReport,
        CommonOptionBag.NoTimeStampForCoverageReport,
        ForcePrune,
      }.Concat(DafnyCommands.ConsoleOutputOptions.Except(new[] { CommonOptionBag.AllowWarnings }).ToList()).
        Concat(DafnyCommands.ResolverOptions);
    }
  }

  private enum Mode {
    Path,
    Block,
    InlinedBlock
  }

  private static readonly Argument<Mode> modeArgument = new("mode", @"
Block - Generate tests targeting block-coverage.
InlinedBlock - Generate tests targeting block coverage after inlining (call-graph sensitive block coverage).
Path - Generate tests targeting path-coverage.");

  public static Command Create() {
    var result = new Command("generate-tests", "(Experimental) Generate Dafny tests that ensure block or path coverage of a particular Dafny program.");
    result.AddArgument(modeArgument);
    result.AddArgument(DafnyCommands.FilesArgument);

    foreach (var option in Options) {
      result.AddOption(option);
    }

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, context) => {
      var mode = context.ParseResult.GetValueForArgument(modeArgument) switch {
        Mode.Path => TestGenerationOptions.Modes.Path,
        Mode.Block => TestGenerationOptions.Modes.Block,
        Mode.InlinedBlock => TestGenerationOptions.Modes.InlinedBlock,
        _ => throw new ArgumentOutOfRangeException()
      };
      PostProcess(options, mode);

      var exitCode = await GenerateTests(options);
      return (int)exitCode;
    });

    return result;
  }

  public static async Task<ExitValue> GenerateTests(DafnyOptions options) {
    var (exitValue, dafnyFiles, _) = await SynchronousCliCompilation.GetDafnyFiles(options);
    if (exitValue != ExitValue.SUCCESS) {
      return exitValue;
    }

    if (dafnyFiles.Count > 1 &&
        options.TestGenOptions.Mode != TestGenerationOptions.Modes.None) {
      await options.OutputWriter.Status(
        "*** Error: Only one .dfy file can be specified for testing");
      return ExitValue.PREPROCESSING_ERROR;
    }

    var dafnyFileNames = DafnyFile.FileNames(dafnyFiles);

    var uri = new Uri(dafnyFileNames[0]);
    var source = new StreamReader(dafnyFileNames[0]);
    var coverageReport = new CoverageReport(name: "Expected Test Coverage", units: "Lines", suffix: "_tests_expected", program: null);
    if (options.TestGenOptions.WarnDeadCode) {
      await foreach (var line in TestGenerator.GetDeadCodeStatistics(source, uri, options, coverageReport)) {
        await options.OutputWriter.Status(line);
      }
    } else {
      await foreach (var line in TestGenerator.GetTestClassForProgram(source, uri, options, coverageReport)) {
        await options.OutputWriter.Status(line);
      }
    }
    if (options.TestGenOptions.CoverageReport != null) {
      await new CoverageReporter(options).SerializeCoverageReports(coverageReport, options.TestGenOptions.CoverageReport);
    }
    if (TestGenerator.SetNonZeroExitCode) {
      exitValue = ExitValue.DAFNY_ERROR;
    }
    return exitValue;
  }

  internal static void PostProcess(DafnyOptions dafnyOptions, TestGenerationOptions.Modes mode) {
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
    dafnyOptions.Set(Snippets.ShowSnippets, false);
    dafnyOptions.TestGenOptions.Mode = mode;
  }

  public static readonly Option<bool> IgnoreWarnings = new("--ignore-warnings",
    "Ignore warnings when generating tests.");

  public static readonly Option<uint> SequenceLengthLimit = new("--length-limit",
    "Add an axiom that sets the length of all sequences to be no greater than <n>. 0 (default) indicates no limit.");

  public static readonly Option<int> LoopUnroll = new("--loop-unroll", () => -1,
    "Higher values can improve accuracy of the analysis at the cost of taking longer to run.");

  public static readonly Option<string> PrintBpl = new("--print-bpl",
    "Print the Boogie code used during test generation.") {
    ArgumentHelpName = "filename"
  };
  public static readonly Option<string> ExpectedCoverageReport = new(["--expected-coverage-report",
    "--coverage-report"
    ],
    "Emit expected test coverage report to a given directory.") {
    ArgumentHelpName = "directory"
  };
  public static readonly Option<bool> ForcePrune = new("--force-prune",
    "Enable axiom pruning that Dafny uses to speed up verification. This may negatively affect the quality of tests.");
  static GenerateTestsCommand() {
    DafnyOptions.RegisterLegacyBinding(IgnoreWarnings, (options, value) => {
      options.TestGenOptions.IgnoreWarnings = value;
    });
    DafnyOptions.RegisterLegacyBinding(LoopUnroll, (options, value) => {
      options.LoopUnrollCount = value;
    });
    DafnyOptions.RegisterLegacyBinding(SequenceLengthLimit, (options, value) => {
      options.TestGenOptions.SeqLengthLimit = value;
    });
    DafnyOptions.RegisterLegacyBinding(PrintBpl, (options, value) => {
      options.TestGenOptions.PrintBpl = value;
    });
    DafnyOptions.RegisterLegacyBinding(ExpectedCoverageReport, (options, value) => {
      options.TestGenOptions.CoverageReport = value;
    });
    DafnyOptions.RegisterLegacyBinding(ForcePrune, (options, value) => {
      options.TestGenOptions.ForcePrune = value;
    });

    OptionRegistry.RegisterOption(LoopUnroll, OptionScope.Cli);
    OptionRegistry.RegisterOption(SequenceLengthLimit, OptionScope.Cli);
    OptionRegistry.RegisterOption(PrintBpl, OptionScope.Cli);
    OptionRegistry.RegisterOption(ExpectedCoverageReport, OptionScope.Cli);
    OptionRegistry.RegisterOption(ForcePrune, OptionScope.Cli);
    OptionRegistry.RegisterOption(IgnoreWarnings, OptionScope.Cli);
  }
}
