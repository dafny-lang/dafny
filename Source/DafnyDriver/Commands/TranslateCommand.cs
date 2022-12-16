using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class TranslateCommand : ICommandSpec {
  public IEnumerable<Option> Options =>
    new Option[] {
      CommonOptionBag.Output,
      CommonOptionBag.CompileVerbose,
      CommonOptionBag.IncludeRuntime,
    }.Concat(ICommandSpec.ExecutionOptions).
      Concat(ICommandSpec.ConsoleOutputOptions).
      Concat(ICommandSpec.CommonOptions);

  public Command Create() {
    var result = new Command("translate", "Generate source and build files in a specified target language.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
    var noVerify = dafnyOptions.Get(BoogieOptionBag.NoVerify);
    dafnyOptions.SpillTargetCode = noVerify ? 3U : 2U;
  }
}
