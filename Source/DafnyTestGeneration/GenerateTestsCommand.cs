using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny; 

public class GenerateTestsCommand : ICommandSpec {
  public IEnumerable<Option> Options =>
    new Option[] {
      LoopUnroll,
      SequenceLengthLimit,
      Target,
      TestInlineDepth,
      BoogieOptionBag.VerificationTimeLimit,
    }.Concat(ICommandSpec.ConsoleOutputOptions).
      Concat(ICommandSpec.ResolverOptions);

  enum Mode {
    Path,
    Block
  }

  readonly Argument<Mode> modeArgument = new("mode", @"
block - Prints block-coverage tests for the given program.
path - Prints path-coverage tests for the given program.");

  public Command Create() {
    var result = new Command("generate-tests", "(Experimental) Generate Dafny tests that ensure block or path coverage of a particular Dafny program.");
    result.AddArgument(modeArgument);
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.CompilerName = "cs";
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = false;
    dafnyOptions.ForceCompile = false;
    dafnyOptions.CompileVerbose = false;
    dafnyOptions.ForbidNondeterminism = true;
    dafnyOptions.DefiniteAssignmentLevel = 2;

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
  public static readonly Option<uint> TestInlineDepth = new("--inline-depth",
    "0 is the default. When used in conjunction with --target-method, this argument specifies the depth up to which all non-tested methods should be inlined.") {
  };
  public static readonly Option<int> SequenceLengthLimit = new("--length-limit",
    "Add an axiom that sets the length of all sequences to be no greater than <n>. -1 indicates no limit.") {
  };
  public static readonly Option<int> LoopUnroll = new("--loop-unroll",
    "Higher values can improve accuracy of the analysis at the cost of taking longer to run.") {
  };
  static GenerateTestsCommand() {
    DafnyOptions.RegisterLegacyBinding(LoopUnroll, (options, value) => {
      options.LoopUnrollCount = value;
    });
    DafnyOptions.RegisterLegacyBinding(SequenceLengthLimit, (options, value) => {
      options.TestGenOptions.SeqLengthLimit = value == -1 ? null : (uint)Math.Abs(value);
    });
    DafnyOptions.RegisterLegacyBinding(TestInlineDepth, (options, value) => {
      options.TestGenOptions.TestInlineDepth = value;
    });
    DafnyOptions.RegisterLegacyBinding(Target, (options, value) => {
      options.TestGenOptions.TargetMethod = value;
    });
  }
}
