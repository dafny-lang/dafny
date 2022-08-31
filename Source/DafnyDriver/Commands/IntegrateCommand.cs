using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

class IntegrateCommand : ICommandSpec {
  public string Name => "integrate";
  public string Description => "Generate source and build files in a specified target language.";
  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.EmitExecutable = false;
    var noVerify = NoVerifyOption.Instance.Get(options);
    dafnyOptions.SpillTargetCode = noVerify ? 3U : 2U;
  }

  public IEnumerable<IOptionSpec> Options =>
    new IOptionSpec[] {
      OutputOption.Instance,
      TargetOption.Instance,
      NoVerifyOption.Instance,
      // CompileVerboseOption.Instance,
      UseRuntimeLibOption.Instance,
    }.Concat(CommandRegistry.CommonOptions);
}