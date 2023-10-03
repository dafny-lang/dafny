using System.Collections.Generic;
using System.CommandLine;

namespace Microsoft.Dafny;

static class DocCommand {

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
  }.Concat(DafnyCommands.ResolverOptions);

  static DocCommand() {
    DafnyCore.DooFile.RegisterNoChecksNeeded(
      DocProgramNameOption,
      DocFilenameFormat,
      DocShowModifyTime
    );
  }

  public static IEnumerable<Option> Options => DocOptions;

  public static Command Create() {
    var result = new Command("doc", @"[Experimental] Create a description page for each module. Files are placed in the folder specified by --output (default is ./docs).");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }
    DafnyCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, _) => {
      options.AllowSourceFolders = true;
      var exitValue = await DafnyDoc.DoDocumenting(options);
      return (int)exitValue;
    });
    return result;
  }
}
