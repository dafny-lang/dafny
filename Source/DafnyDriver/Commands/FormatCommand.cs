using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class FormatCommand : ICommandSpec {

  public IEnumerable<IOptionSpec> Options =>
    new IOptionSpec[] {
      CheckOption.Instance,
      PrintOption.Instance,
      PluginOption.Instance,
      UseBaseFileNameOption.Instance,
    };

  public Command Create() {
    var result = new Command("format", @"Format the dafny file in-place.
If no dafny file is provided, will look for every available Dafny file.
Use -print:- to output the content of the formatted files instead of overwriting them.");
    result.AddArgument(CommandRegistry.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Format = true;
    dafnyOptions.Compile = false;
    dafnyOptions.FormatCheck = CheckOption.Instance.Get(options);
    dafnyOptions.PrintFile = PrintOption.Instance.Get(options);
  }
}
