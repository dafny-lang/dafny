using System.CommandLine;

namespace Microsoft.Dafny;

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
      return CompilerDriver.RunCompiler(options);
    });
    return result;
  }
}