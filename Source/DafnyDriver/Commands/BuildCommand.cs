using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class BuildCommand : ICommandSpec {
  public IEnumerable<Option> Options => new Option[] {
    CommonOptionBag.Output,
  }.Concat(ICommandSpec.ExecutionOptions).
    Concat(ICommandSpec.ConsoleOutputOptions).
    Concat(ICommandSpec.ResolverOptions);

  public Command Create() {
    var result = new Command("build", "Produce an executable binary or a library.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = false;
    dafnyOptions.ForceCompile = dafnyOptions.Get(BoogieOptionBag.NoVerify);
  }
}
