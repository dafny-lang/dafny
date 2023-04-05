using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class DocCommand : ICommandSpec {

  public static readonly Option<string> DocProgramNameOption = new("--doc-program-name",
    "The text to use as program name in generated documentation"
  );


  public static IEnumerable<Option> DocOptions => new Option[] {
    CommonOptionBag.Verbose,
    CommonOptionBag.Output,
    DocProgramNameOption
  }.Concat(ICommandSpec.ResolverOptions);

  static DocCommand() {
    DafnyOptions.RegisterLegacyBinding(DocProgramNameOption, (options, value) => { options.DocProgramNameOption = value; });
  }

  public IEnumerable<Option> Options => DocOptions;

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
    if (dafnyOptions.DocProgramNameOption == null) {

    }
  }
}
