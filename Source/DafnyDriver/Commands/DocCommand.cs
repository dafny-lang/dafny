using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class DocCommand : ICommandSpec {

  public static readonly Option<string> DocProgramNameOption = new("--program-name",
    "[doc] The text to use as program name in generated documentation"
  );

  public static readonly Option<string> DocFilenameFormat = new("--file-name",
    "[doc] Form of file references in documentation: none, absolute, name (the default), relative=<prefix>"
  );

  public static readonly Option<bool> DocShowModifyTime = new("--modify-time",
    "[doc] If enabled, includes the last modified time of source files in the generated documentation"
  );


  public static IEnumerable<Option> DocOptions => new Option[] {
    CommonOptionBag.Output,
    DocProgramNameOption,
    DocFilenameFormat,
    DocShowModifyTime,
  }.Concat(ICommandSpec.ResolverOptions);

  public DocCommand() {
    DafnyCore.DooFile.RegisterNoChecksNeeded(
      DocProgramNameOption,
      DocFilenameFormat,
      DocShowModifyTime
    );
  }

  public IEnumerable<Option> Options => DocOptions;

  public Command Create() {
    var result = new Command("doc", @"[Experimental] Create a description page for each module. Files are placed in the folder specified by --output (default is ./docs).");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
    dafnyOptions.DafnyVerify = false;
    dafnyOptions.AllowSourceFolders = true;
  }
}
