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
      options.Set(DafnyFile.DoNotVerifyDependencies, true);
      var compilation = CliCompilation.Create(options);
      compilation.Compilation.ShouldProcessSolverOptions = false;
      compilation.Start();
      await compilation.Resolution;

      var value = await compilation.GetAndReportExitValue();
      if (value == ExitValue.SUCCESS) {
        await options.OutputWriter.WriteLineAsync("\nDafny program verifier did not attempt verification");
      }
      return (int)value;
    });
    return result;
  }
}