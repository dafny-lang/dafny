using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

class RunCommand : ICommandSpec {
  public string Name => "run";
  public string Description => "Run the program.";

  public IEnumerable<IOptionSpec> Options =>
    new IOptionSpec[] {
      TargetOption.Instance,
      NoVerifyOption.Instance,
    }.Concat(CommandRegistry.CommonOptions);

  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = true;
    dafnyOptions.ForceCompile = NoVerifyOption.Instance.Get(options);
    dafnyOptions.CompileVerbose = false;
  }
}
