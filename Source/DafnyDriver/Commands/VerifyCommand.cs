using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;

namespace Microsoft.Dafny;

class VerifyCommand : ICommandSpec {
  public IEnumerable<IOptionSpec> Options => CommandRegistry.CommonOptions;

  public Command Create() {
    var result = new Command("verify", "Verify the program.");
    result.AddArgument(CommandRegistry.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
  }
}