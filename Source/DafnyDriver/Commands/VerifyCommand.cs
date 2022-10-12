using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;

namespace Microsoft.Dafny;

class VerifyCommand : ICommandSpec {
  public string Name => "verify";
  public string Description => "Verify the program.";
  public IEnumerable<IOptionSpec> Options => CommandRegistry.CommonOptions;
  
  public Command Create() {
    var result = new Command(Name, Description);
    result.AddArgument(CommandRegistry.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
    foreach (var file in context.ParseResult.GetValueForArgument(CommandRegistry.FilesArgument)) {
      dafnyOptions.AddFile(file.FullName);
    }
  }
}