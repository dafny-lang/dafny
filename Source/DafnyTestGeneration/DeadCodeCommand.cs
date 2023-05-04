using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

public class DeadCodeCommand : ICommandSpec {
  public IEnumerable<Option> Options =>
    new Option[] {
      // IMPORTANT: Before adding new options, make sure they are
      // appropriately copied over in the GenerateTestCommand.CopyForProcedure method 
      GenerateTestsCommand.LoopUnroll,
      GenerateTestsCommand.SequenceLengthLimit,
      BoogieOptionBag.SolverLog,
      BoogieOptionBag.SolverOption,
      BoogieOptionBag.SolverPath,
      BoogieOptionBag.SolverResourceLimit,
      BoogieOptionBag.VerificationTimeLimit
    }.Concat(ICommandSpec.ConsoleOutputOptions).
      Concat(ICommandSpec.ResolverOptions);

  public Command Create() {
    var result = new Command("find-dead-code", "(Experimental) Use counterexample generation to warn about potential dead code.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    // IMPORTANT: Before adding new default options, make sure they are
    // appropriately copied over in the GenerateTestCommand.CopyForProcedure method 
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
