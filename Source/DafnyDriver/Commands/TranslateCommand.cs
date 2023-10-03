using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

static class TranslateCommand {
  public static IEnumerable<Option> Options =>
    new Option[] {
      CommonOptionBag.Output,
      CommonOptionBag.IncludeRuntimeOption,
    }.Concat(DafnyCommands.TranslationOptions).
      Concat(DafnyCommands.ConsoleOutputOptions).
      Concat(DafnyCommands.ResolverOptions);

  public static Command Create() {
    var result = new Command("translate", "Translate Dafny sources to source and build files in a specified language.");

    result.AddCommand(new Command("cs", "C#"));
    result.AddCommand(new Command("go", "GoLang"));
    result.AddCommand(new Command("js", "JavaScript"));
    result.AddCommand(new Command("java"));
    result.AddCommand(new Command("py", "Python"));
    result.AddCommand(new Command("cpp", "C++. This back-end has various limitations (see Docs/Compilation/Cpp.md). This includes lack of support for BigIntegers (aka int), most higher order functions, and advanced features like traits or co-inductive types."));

    foreach (var subCommand in result.Subcommands) {
      subCommand.AddArgument(DafnyCommands.FilesArgument);

      foreach (var option in Options) {
        subCommand.AddGlobalOption(option);
      }

      DafnyCli.SetHandlerUsingDafnyOptionsContinuation(subCommand, async (options, context) => {
        options.Compile = false;
        var noVerify = options.Get(BoogieOptionBag.NoVerify);
        options.CompilerName = subCommand.Name;
        options.SpillTargetCode = noVerify ? 3U : 2U;
        var continueCliWithOptions = await DafnyPipelineDriver.ContinueCliWithOptions(options);
        return continueCliWithOptions;
      });
    }

    return result;
  }
}
