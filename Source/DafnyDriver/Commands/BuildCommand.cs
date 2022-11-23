using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class BuildCommand : ICommandSpec {
  public IEnumerable<IOptionSpec> Options => new IOptionSpec[] {
    OutputOption.Instance,
    TargetOption.Instance,
    CompileVerboseOption.Instance,
    VerificationTimeLimitOption.Instance,
  }.Concat(ICommandSpec.ExecutionOptions).
    Concat(ICommandSpec.CommonOptions);

  public Command Create() {
    var result = new Command("build", "Produce an executable binary or a library.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = false;
    dafnyOptions.ForceCompile = NoVerifyOption.Instance.Get(options);
  }
}
