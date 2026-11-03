using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using DafnyCore;
using DafnyTestGeneration;
using Microsoft.Boogie;
using DafnyDriver.Commands;
using System.Diagnostics;
using System.Globalization;

// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
namespace Microsoft.Dafny;

static class GenerateTestsCommand {
  public static IEnumerable<Option> Options {
    get {
      return new Option[] {
        Fdnf,
        Bva,
        Simplify,
        Repeat,
        Time,
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
    InlinedBlock,
    Spec
  }

  private static readonly Argument<Mode> modeArgument = new("mode", @"
Block - Generate tests targeting block-coverage.
InlinedBlock - Generate tests targeting block coverage after inlining (call-graph sensitive block coverage).
Path - Generate tests targeting path-coverage.
Spec - Generate specification-based tests.");

  public static Command Create() {
    var result = new Command("generate-tests", "(Experimental) Generate Dafny tests that ensure block or path coverage of a particular Dafny program.");
    result.AddArgument(modeArgument);
    result.AddArgument(DafnyCommands.FilesArgument);

    foreach (var option in Options) {
      result.AddOption(option);
    }

    result.AddValidator(commandResult => {
      var mode = commandResult.GetValueForArgument(modeArgument);
      var hasFdnf = commandResult.FindResultFor(Fdnf) is not null;
      var hasBva = commandResult.FindResultFor(Bva) is not null;
      var hasSimplify = commandResult.FindResultFor(Simplify) is not null;

      if (mode != Mode.Spec) {
        var invalidFlags = new List<string>();
        if (hasFdnf) {
          invalidFlags.Add("--fdnf");
        }
        if (hasBva) {
          invalidFlags.Add("--bva");
        }
        if (hasSimplify) {
          invalidFlags.Add("--simplify");
        }

        if (invalidFlags.Count > 0) {
          commandResult.ErrorMessage =
            $"*** Error: The following options can only be used when the mode is 'Spec': {string.Join(", ", invalidFlags)}";
        }
      }
    });

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, context) => {
      var mode = context.ParseResult.GetValueForArgument(modeArgument) switch {
        Mode.Path => TestGenerationOptions.Modes.Path,
        Mode.Block => TestGenerationOptions.Modes.Block,
        Mode.InlinedBlock => TestGenerationOptions.Modes.InlinedBlock,
        Mode.Spec => TestGenerationOptions.Modes.Spec,
        _ => throw new ArgumentOutOfRangeException()
      };
      PostProcess(options, mode);

      var exitCode = await GenerateTests(options);
      options.TestGenOptions.StopWatch.Stop();
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

    options.TestGenOptions.FailedVerification = await GetUnverified(options);

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

  public static async Task<HashSet<String>> GetUnverified(DafnyOptions options) {
    HashSet<String> unverified = [];
    object unverifiedLock = new object();

    if (options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
      options.TrackVerificationCoverage = true;
    }

    var compilation = CliCompilation.Create(options);
    compilation.Start();

    var resolution = await compilation.Resolution;

    if (resolution != null) {
      var tcs = new TaskCompletionSource<bool>();
      var verification = compilation.VerifyAllLazily().ToObservable();

      verification.Subscribe(
        onNext: result => {
          bool verified = true;

          foreach (var taskResult in result.Results) {
            var outcome = taskResult.Result.Outcome;
            if (outcome != SolverOutcome.Valid && outcome != SolverOutcome.Bounded) {
              verified = false;
              break;
            }
          }

          if (!verified) {
            lock (unverifiedLock) {
              unverified.Add(result.CanVerify.FullDafnyName);
            }
          }

        },
        onError: ex => tcs.SetException(ex),
        onCompleted: () => tcs.SetResult(true)
        );

      await tcs.Task;
    }

    return unverified;
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
    dafnyOptions.TestGenOptions.StopWatch = Stopwatch.StartNew();
  }

  public static readonly Option<bool> Fdnf = new("--fdnf",
    "Only for the Spec mode. It calculates the full DNF, instead of the safe DNF (default)." +
    "Produces all 2^N − 1 non-empty subsets of branch satisfaction. For A || B: branches A ∧ B, A ∧ !B, !A ∧ B." +
    "Generates more clauses (more test scenarios) but drops the short-circuit-safety guarantee: tests may evaluate " +
    "guarded subexpressions where the guard is false, potentially causing runtime errors" +
    "(e.g.: out-of-bounds, division by zero).");

  public static readonly Option<int?> Bva = new(
    name: "--bva",
    description: "Only for the Spec mode. Adds Boundary Value Analysis to test generation. Optionally accepts a numeric limit (default: 2147483647).",
    parseArgument: result => {
      if (result.Tokens.Count == 0) {
        return int.MaxValue;
      }

      if (int.TryParse(result.Tokens[0].Value, out var customValue)) {
        return customValue;
      }

      result.ErrorMessage = $"Cannot parse '{result.Tokens[0].Value}' as a valid integer for --bva.";
      return null;
    }
  ) {
    Arity = ArgumentArity.ZeroOrOne
  };

  public static readonly Option<bool> Simplify = new("--simplify",
    "Only for Spec mode. Simplifies test output by including only input and output values." +
    "In other words, removes 'expect' statements related to pre and post condition, whenever possible, so tests" +
    "are more easily understood.");

  public static readonly Option<uint> Repeat = new("--repeat", () => 1,
    "Repeats the pipeline <n> times, in order to generate, approximately, <n> times more tests than the initial iteration. " +
    "1 (default) indicates no repetition.");

  public static readonly Option<bool> Time = new("--time",
    "Prints the elapsed time since the beginning of the program (in seconds), split by repeat section.");

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
    DafnyOptions.RegisterLegacyBinding(Fdnf, (options, value) => {
      options.TestGenOptions.Fdnf = value;
    });
    DafnyOptions.RegisterLegacyBinding(Bva, (options, value) => {
      options.TestGenOptions.Bva = value;
    });
    DafnyOptions.RegisterLegacyBinding(Simplify, (options, value) => {
      options.TestGenOptions.Simplify = value;
    });
    DafnyOptions.RegisterLegacyBinding(Repeat, (options, value) => {
      options.TestGenOptions.Repeat = value;
    });
    DafnyOptions.RegisterLegacyBinding(Time, (options, value) => {
      options.TestGenOptions.Time = value;
    });
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

    OptionRegistry.RegisterOption(Fdnf, OptionScope.Cli);
    OptionRegistry.RegisterOption(Bva, OptionScope.Cli);
    OptionRegistry.RegisterOption(Simplify, OptionScope.Cli);
    OptionRegistry.RegisterOption(Repeat, OptionScope.Cli);
    OptionRegistry.RegisterOption(Time, OptionScope.Cli);
    OptionRegistry.RegisterOption(LoopUnroll, OptionScope.Cli);
    OptionRegistry.RegisterOption(SequenceLengthLimit, OptionScope.Cli);
    OptionRegistry.RegisterOption(PrintBpl, OptionScope.Cli);
    OptionRegistry.RegisterOption(ExpectedCoverageReport, OptionScope.Cli);
    OptionRegistry.RegisterOption(ForcePrune, OptionScope.Cli);
    OptionRegistry.RegisterOption(IgnoreWarnings, OptionScope.Cli);
  }
}
