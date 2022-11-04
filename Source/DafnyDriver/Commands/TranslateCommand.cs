using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class TranslateCommand : ICommandSpec {
  public Command Create() {
    var result = new Command("translate", "Generate source and build files in a specified target language.");
    result.AddArgument(CommandRegistry.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
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