using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny; 

public class DeadCodeCommand : ICommandSpec {
  public IEnumerable<Option> Options =>
    new Option[] {
      GenerateTestsCommand.LoopUnroll,
      GenerateTestsCommand.SequenceLengthLimit,
      BoogieOptionBag.VerificationTimeLimit,
    }.Concat(ICommandSpec.ConsoleOutputOptions).
      Concat(ICommandSpec.CommonOptions);

  public Command Create() {
    var result = new Command("find-dead-code", "(Experimental) Use counterexample generation to warn about potential dead code.");
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

    dafnyOptions.TestGenOptions.Mode = TestGenerationOptions.Modes.Block;
    dafnyOptions.TestGenOptions.WarnDeadCode = true;
  }
}
