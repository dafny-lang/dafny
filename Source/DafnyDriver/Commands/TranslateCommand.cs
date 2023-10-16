using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using Microsoft.Dafny.Compilers;

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
        subCommand.AddGlobalOption(option);
      }

      DafnyCli.SetHandlerUsingDafnyOptionsContinuation(subCommand, async (options, context) => {
        options.Compile = false;
        var noVerify = options.Get(BoogieOptionBag.NoVerify);
        options.CompilerName = subCommand.Name;
        options.SpillTargetCode = noVerify ? 3U : 2U;
        var continueCliWithOptions = await CompilerDriver.RunCompiler(options);
        return continueCliWithOptions;
      });
    }

    return result;
  }
}
