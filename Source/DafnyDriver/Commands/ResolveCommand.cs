using System;
using System.CommandLine;
using DafnyDriver.Commands;

namespace Microsoft.Dafny;

static class ResolveCommand {

  public static Command Create() {
    var result = new Command("resolve", "Only check for parse and type resolution errors.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in DafnyCommands.ConsoleOutputOptions.Concat(DafnyCommands.ResolverOptions)) {
      result.AddOption(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, _) => {
      var compilation = CliCompilation.Create(options);
      compilation.Start();
      try {
        await compilation.Resolution;
      } catch (OperationCanceledException) {
      }

      if (compilation.ExitValue == ExitValue.SUCCESS) {
        await options.OutputWriter.WriteLineAsync("\nDafny program verifier did not attempt verification");
      }
      return compilation.ExitCode;
    });
    return result;
  }
}