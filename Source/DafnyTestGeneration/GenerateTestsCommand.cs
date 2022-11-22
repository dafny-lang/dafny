using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny; 

public class GenerateTestsCommand : ICommandSpec {
  public IEnumerable<IOptionSpec> Options =>
    new IOptionSpec[] {
      LoopUnrollOption.Instance,
      SequenceLengthLimitOption.Instance,
      TargetMethod.Instance,
      TestInlineDepth.Instance,
      VerificationTimeLimitOption.Instance,
    }.Concat(ICommandSpec.CommonOptions);

  enum Mode {
    Path,
    Block
  }

  readonly Argument<Mode> modeArgument = new("mode", @"
block - Prints block-coverage tests for the given program.
path - Prints path-coverage tests for the given program.");

  public Command Create() {
    var result = new Command("generate-tests", "(Experimental) Generate Dafny tests that ensure block or path coverage of a particular Dafny program .");
    result.AddArgument(modeArgument);
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
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
}

class TargetMethod : StringOption {
  public static readonly TargetMethod Instance = new();
  public override object DefaultValue => null!;
  public override string LongName => "target-method";
  public override string ArgumentName => "name";
  public override string Description => "If specified, only this method will be tested.";
  public override string PostProcess(DafnyOptions options) {
    options.TestGenOptions.TargetMethod = Get(options);
    return null!;
  }
}

class TestInlineDepth : NaturalNumberOption {
  public static readonly TestInlineDepth Instance = new();
  public override object DefaultValue => 0u;
  public override string LongName => "inline-depth";
  public override string ArgumentName => "n";
  public override string Description =>
    "0 is the default. When used in conjunction with --target-method, this argument specifies the depth up to which all non-tested methods should be inlined.";
  public override string PostProcess(DafnyOptions options) {
    options.TestGenOptions.TestInlineDepth = Get(options);
    return null!;
  }
}

class SequenceLengthLimitOption : IntegerOption {
  public static readonly SequenceLengthLimitOption Instance = new();
  public override object DefaultValue => -1;
  public override string LongName => "length-limit";
  public override string ArgumentName => "n";
  public override string Description => "Add an axiom that sets the length of all sequences to be no greater than <n>. -1 indicates no limit.";

  public override string PostProcess(DafnyOptions options) {
    var limit = Get(options);
    options.TestGenOptions.SeqLengthLimit = limit == -1 ? null : (uint)Math.Abs(limit);
    return null!;
  }
}

class LoopUnrollOption : IntegerOption {
  public static readonly LoopUnrollOption Instance = new();
  public override object DefaultValue => 0;
  public override string LongName => "loop-unroll";
  public override string ArgumentName => "n";
  public override string Description => "Higher values can improve accuracy of the analysis at the cost of taking longer to run.";
  public override string PostProcess(DafnyOptions options) {
    options.LoopUnrollCount = Get(options);
    return null!;
  }
}
