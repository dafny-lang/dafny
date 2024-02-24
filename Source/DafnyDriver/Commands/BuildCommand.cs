using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny;

public static class BuildCommand {

  public static IEnumerable<Option> Options => new Option[] {
    CommonOptionBag.Output,
  }.Concat(DafnyCommands.ExecutionOptions).
  Concat(DafnyCommands.ConsoleOutputOptions).
  Concat(DafnyCommands.ResolverOptions);
  public static Command Create() {
    var result = new Command("build", "Produce an executable binary or a library.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => {
      options.Compile = true;
      options.RunAfterCompile = false;
      options.ForceCompile = options.Get(BoogieOptionBag.NoVerify);
      options.OutputWriter.WriteLine("Using --target has been deprecated. Please move to the subcommand cli");

      return SynchronousCliCompilation.Run(options);
    });

    foreach (var backend in SinglePassCompiler.Plugin.GetCompilers(DafnyOptions.Default)) {
      var command = backend.GetCommand();
      result.AddCommand(command);
      if (!backend.IsStable) {
        command.IsHidden = true;
      }
    }

    foreach (var subCommand in result.Subcommands) {
      subCommand.AddArgument(DafnyCommands.FilesArgument);

      foreach (var option in Options) {
        subCommand.AddOption(option);
      }
      DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(subCommand, (options, _) => {
        options.Compile = true;
        options.RunAfterCompile = false;
        options.ForceCompile = options.Get(BoogieOptionBag.NoVerify);
        options.CompilerName = subCommand.Name;

        return SynchronousCliCompilation.Run(options);
      });
    }

    return result;
  }
}
