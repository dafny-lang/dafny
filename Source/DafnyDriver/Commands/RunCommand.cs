using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using DafnyCore;

namespace Microsoft.Dafny;

class RunCommand : ICommandSpec {
  private readonly Argument<IEnumerable<string>> userProgramArguments;

  public static readonly Option<IEnumerable<string>> Inputs = new("--input", "Specify an additional input file.") {
    ArgumentHelpName = "file"
  };

  static RunCommand() {
    DafnyOptions.RegisterLegacyBinding(Inputs, (options, files) => {
      foreach (var file in files) {
        options.AddFile(file);
      }
    });
    
    DooFile.RegisterLibraryChecks(noChecksNeeded: new Option[] {
      Inputs
    });
  }

  public IEnumerable<Option> Options =>
    new Option[] {
      Inputs,
    }.Concat(ICommandSpec.ExecutionOptions).
      Concat(ICommandSpec.ConsoleOutputOptions).
      Concat(ICommandSpec.ResolverOptions);

  public RunCommand() {
    userProgramArguments = new Argument<IEnumerable<string>>("program-arguments", "arguments to the Dafny program");
    userProgramArguments.SetDefaultValue(new List<string>());
  }

  public Command Create() {
    var result = new Command("run", "Run the program.");
    result.AddArgument(CommandRegistry.FileArgument);
    result.AddArgument(userProgramArguments);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.MainArgs = context.ParseResult.GetValueForArgument(userProgramArguments).ToList();
    var inputFile = context.ParseResult.GetValueForArgument(CommandRegistry.FileArgument);
    dafnyOptions.AddFile(inputFile.FullName);
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = true;
    dafnyOptions.ForceCompile = dafnyOptions.Get(BoogieOptionBag.NoVerify);
    dafnyOptions.CompileVerbose = false;
  }
}
