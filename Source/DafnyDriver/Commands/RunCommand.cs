using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class RunCommand : ICommandSpec {
  private readonly Argument<IEnumerable<string>> userProgramArguments;

  public IEnumerable<IOptionSpec> Options =>
    new IOptionSpec[] {
      TargetOption.Instance,
      NoVerifyOption.Instance,
      InputsOption.Instance,
    }.Concat(CommandRegistry.CommonOptions);

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
    dafnyOptions.ForceCompile = NoVerifyOption.Instance.Get(options);
    dafnyOptions.CompileVerbose = false;
  }
}
