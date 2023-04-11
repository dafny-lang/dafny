using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class DocCommand : ICommandSpec {

  public static readonly Option<string> DocProgramNameOption = new("--doc-program-name",
    "The text to use as program name in generated documentation"
  );

  public static readonly Option<string> DocFilenameFormat = new("--doc-file-name",
    "Form of file references in documentation: none, absolute, name (the default), relative=<prefix>"
  );

  public static readonly Option<bool> DocShowModifyTime = new("--doc-modify-time",
    "If enabled, includes the last modified time of source files in the output"
  );


  public static IEnumerable<Option> DocOptions => new Option[] {
    CommonOptionBag.Verbose,
    CommonOptionBag.Output,
    DocProgramNameOption,
    DocFilenameFormat,
    DocShowModifyTime,
  }.Concat(ICommandSpec.ResolverOptions);

  static DocCommand() {
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
  }
}
