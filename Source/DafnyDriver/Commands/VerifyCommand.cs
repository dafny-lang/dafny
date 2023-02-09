using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class VerifyCommand : ICommandSpec {
  public IEnumerable<Option> Options => new Option[] {
    BoogieOptionBag.BoogieFilter,
  }.Concat(ICommandSpec.VerificationOptions).
    Concat(ICommandSpec.ConsoleOutputOptions).
    Concat(ICommandSpec.ResolverOptions);

  public Command Create() {
    var result = new Command("verify", "Verify the program.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
  }
}

class ResolveCommand : ICommandSpec {
  public IEnumerable<Option> Options => ICommandSpec.ConsoleOutputOptions.
    Concat(ICommandSpec.ResolverOptions);

  public Command Create() {
    var result = new Command("resolve", "Only check for parse and type resolution errors.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
    dafnyOptions.Verify = false;
  }
}
