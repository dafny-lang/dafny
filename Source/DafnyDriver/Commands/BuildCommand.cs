using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

class BuildCommand : ICommandSpec {
  public string Name => "build";

  public string Description => "Produce an executable binary.";

  public IEnumerable<IOptionSpec> Options => new IOptionSpec[] {
    OutputOption.Instance,
    TargetOption.Instance,
    NoVerifyOption.Instance,
    CompileVerboseOption.Instance,
  }.Concat(CommandRegistry.CommonOptions);

  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = false;
    dafnyOptions.ForceCompile = NoVerifyOption.Instance.Get(options);
    dafnyOptions.CompileVerbose = false;
  }
}
