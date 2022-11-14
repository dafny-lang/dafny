using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny; 

public class TestCommand : ICommandSpec {
  public IEnumerable<IOptionSpec> Options =>
    new IOptionSpec[] {
      TargetOption.Instance,
      NoVerifyOption.Instance,
      EnforceDeterminismOption.Instance,
      VerificationTimeLimitOption.Instance,
    }.Concat(ICommandSpec.CommonOptions);

  public Command Create() {
    var result = new Command("test", "(Experimental) Execute every method in the program that's annotated with the {:test} attribute.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = true;
    dafnyOptions.RunAllTests = true;
    dafnyOptions.ForceCompile = NoVerifyOption.Instance.Get(options);
    dafnyOptions.CompileVerbose = false;
  }
}