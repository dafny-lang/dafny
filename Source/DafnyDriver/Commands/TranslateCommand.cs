using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

class TranslateCommand : ICommandSpec {
  public string Name => "translate";
  public string Description => "Generate source and build files in a specified target language.";
  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.Compile = false;
    var noVerify = NoVerifyOption.Instance.Get(options);
    dafnyOptions.SpillTargetCode = noVerify ? 3U : 2U;
  }

  public IEnumerable<IOptionSpec> Options =>
    new IOptionSpec[] {
      OutputOption.Instance,
      TargetOption.Instance,
      NoVerifyOption.Instance,
      CompileVerboseOption.Instance,
      IncludeRuntimeOption.Instance,
    }.Concat(CommandRegistry.CommonOptions);
}