using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.IO;
using System.Linq;
using DafnyCore;

namespace Microsoft.Dafny;

static class RunCommand {
  private static readonly Argument<IEnumerable<string>> UserProgramArguments;

  public static readonly Option<IEnumerable<string>> Inputs = new("--input", "Specify an additional input file.") {
    ArgumentHelpName = "file"
  };

  static RunCommand() {
    UserProgramArguments = new Argument<IEnumerable<string>>("program-arguments", "arguments to the Dafny program");
    UserProgramArguments.SetDefaultValue(new List<string>());
    
    DafnyOptions.RegisterLegacyBinding(Inputs, (options, files) => {
      foreach (var file in files) {
        options.CliRootSourceUris.Add(new Uri(Path.GetFullPath(file)));
      }
    });

    DooFile.RegisterNoChecksNeeded(
      Inputs
    );
  }

  public static IEnumerable<Option> Options =>
    new Option[] {
      Inputs,
    }.Concat(DafnyCommands.ExecutionOptions).
      Concat(DafnyCommands.ConsoleOutputOptions).
      Concat(DafnyCommands.ResolverOptions);

  public static Command Create() {
    var result = new Command("run", "Run the program.");
    result.AddArgument(DafnyCli.FileArgument);
    result.AddArgument(UserProgramArguments);
    foreach (var option in Options) {
      
    }
    DafnyCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, context) => {
      options.MainArgs = context.ParseResult.GetValueForArgument(UserProgramArguments).ToList();
      var inputFile = context.ParseResult.GetValueForArgument(DafnyCli.FileArgument);
      options.CliRootSourceUris.Add(new Uri(Path.GetFullPath(inputFile.FullName)));
      options.Compile = true;
      options.RunAfterCompile = true;
      options.ForceCompile = options.Get(BoogieOptionBag.NoVerify);
      return DafnyDriver.ContinueCliWithOptions(options);
    });
    return result;
  }
}
