using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public static class VerifyCommand {

  public static Command Create() {
    var result = new Command("verify", "Verify the program.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in new Option[] {
                 BoogieOptionBag.BoogieFilter,
               }.Concat(DafnyCommands.VerificationOptions).
               Concat(DafnyCommands.ConsoleOutputOptions).
               Concat(DafnyCommands.ResolverOptions)) {
      result.AddOption(option);
    }
    DafnyCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => {
      options.Compile = false;
      return DafnyPipelineDriver.ContinueCliWithOptions(options);
    });
    return result;
  }
}

static class ResolveCommand {

  public static Command Create() {
    var result = new Command("resolve", "Only check for parse and type resolution errors.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in DafnyCommands.ConsoleOutputOptions.Concat(DafnyCommands.ResolverOptions)) {
      result.AddOption(option);
    }
    DafnyCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => {
      options.Compile = false;
      options.Verify = false;
      return DafnyPipelineDriver.ContinueCliWithOptions(options);
    });
    return result;
  }
}
