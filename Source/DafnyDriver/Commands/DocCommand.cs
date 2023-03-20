using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class DocCommand : ICommandSpec {

  public IEnumerable<Option> Options => ICommandSpec.DocOptions;

  public Command Create() {
    var result = new Command("doc", @"Create a description page for each module.
Files are placed in the folder specified by --output (default is ./docs).");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
    dafnyOptions.DafnyVerify = false;
    dafnyOptions.AllowSourceFolders = true;
  }
}
