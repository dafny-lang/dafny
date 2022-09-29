using System.Collections.Generic;

namespace Microsoft.Dafny;

class VerifyCommand : ICommandSpec {
  public string Name => "verify";
  public string Description => "Verify the program.";
  public IEnumerable<IOptionSpec> Options => CommandRegistry.CommonOptions;

  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.Compile = false;
  }
}