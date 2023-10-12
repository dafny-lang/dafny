// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

static class DeadCodeCommand {
  public static IEnumerable<Option> Options =>
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
    }.Concat(DafnyCommands.ConsoleOutputOptions).
      Concat(DafnyCommands.ResolverOptions);

  public static Command Create() {
    var result = new Command("find-dead-code", "(Experimental) Use counterexample generation to warn about potential dead code.");
    result.AddArgument(DafnyCommands.FilesArgument);

    foreach (var option in Options) {
      result.AddOption(option);
    }

    DafnyCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, context) => {
      GenerateTestsCommand.PostProcess(options, TestGenerationOptions.Modes.Block);

      options.TestGenOptions.WarnDeadCode = true;
      var exitCode = await GenerateTestsCommand.GenerateTests(options);
      return (int)exitCode;
    });
    return result;
  }
}
