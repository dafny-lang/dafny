using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

public static class BuildCommand {

  public static Command Create() {
    var result = new Command("build", "Produce an executable binary or a library.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in new Option[] {
                 CommonOptionBag.Output,
               }.Concat(DafnyCommands.ExecutionOptions).
               Concat(DafnyCommands.ConsoleOutputOptions).
               Concat(DafnyCommands.ResolverOptions)) {
      result.AddOption(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, context) => {
      options.Compile = true;
      options.CompilerExecutable = context.ParseResult.GetValueForOption(CommonOptionBag.TargetExecPath);
      options.RunAfterCompile = false;
      options.ForceCompile = options.Get(BoogieOptionBag.NoVerify);
      return CompilerDriver.Run(options);
    });
    return result;
  }
}
