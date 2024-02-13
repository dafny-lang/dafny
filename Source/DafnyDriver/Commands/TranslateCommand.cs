using System.Collections.Generic;
using System.CommandLine;
using DafnyCore;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;

static class TranslateCommand {

  static TranslateCommand() {
  }

  public static IEnumerable<Option> Options =>
    new Option[] {
      CommonOptionBag.Output,
      IExecutableBackend.OuterModule,
      CommonOptionBag.IncludeRuntimeOption,
      RunAllTestsMainMethod.IncludeTestRunner
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

      DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(subCommand, async (options, context) => {
        options.Compile = false;
        var noVerify = options.Get(BoogieOptionBag.NoVerify);
        options.CompilerName = subCommand.Name;
        options.SpillTargetCode = noVerify ? 3U : 2U;
        return await SynchronousCliCompilation.Run(options);
      });
    }

    return result;
  }
}
