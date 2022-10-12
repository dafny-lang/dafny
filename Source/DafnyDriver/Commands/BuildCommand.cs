using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
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

  public Command Create() {
    var result = new Command(Name, Description);
    result.AddArgument(CommandRegistry.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {

    foreach (var file in context.ParseResult.GetValueForArgument(CommandRegistry.FilesArgument)) {
      dafnyOptions.AddFile(file.FullName);
    }
    
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = false;
    dafnyOptions.ForceCompile = NoVerifyOption.Instance.Get(options);
    dafnyOptions.CompileVerbose = false;
  }
}
