// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class DeadCodeCommand : ICommandSpec {
  public IEnumerable<Option> Options =>
    new Option[] {
      GenerateTestsCommand.LoopUnroll,
      GenerateTestsCommand.SequenceLengthLimit,
      GenerateTestsCommand.CoverageReport,
      GenerateTestsCommand.ForcePrune,
      GenerateTestsCommand.PrintBpl,
      BoogieOptionBag.SolverLog,
      BoogieOptionBag.SolverOption,
      BoogieOptionBag.SolverOptionHelp,
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
    GenerateTestsCommand.PostProcess(dafnyOptions, options, context, TestGenerationOptions.Modes.Block);
    dafnyOptions.TestGenOptions.WarnDeadCode = true;
  }
}
