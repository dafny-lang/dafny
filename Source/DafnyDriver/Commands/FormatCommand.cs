using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

class FormatCommand : ICommandSpec {
  public string Name => "format";
  public string Description => @"Format the dafny file in-place.
If no dafny file is provided, will look for every available Dafny file.
Use -print:- to output the content of the formatted files instead of overwriting them.";

  public IEnumerable<IOptionSpec> Options =>
    new IOptionSpec[] {
      CheckOption.Instance,
      PrintOption.Instance,
      PluginOption.Instance,
      UseBaseFileNameOption.Instance,
    };

  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.Format = true;
    dafnyOptions.Compile = false;
    dafnyOptions.FormatCheck = CheckOption.Instance.Get(options);
    dafnyOptions.PrintFile = PrintOption.Instance.Get(options);
  }
}
