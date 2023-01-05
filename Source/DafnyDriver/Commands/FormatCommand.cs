using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class FormatCommand : ICommandSpec {

  public static readonly Option<bool> Check = new("--check", () => false, @"
Instead of formatting files, verify that all files are already
formatted through and return a non-zero exit code if it is not the case".TrimStart());

  public IEnumerable<Option> Options => new Option[] {
      Check,
      CommonOptionBag.Plugin,
      DeveloperOptionBag.UseBaseFileName,
      DeveloperOptionBag.Print,
      BoogieOptionBag.BoogieFilter,
    }.
    Concat(ICommandSpec.ConsoleOutputOptions).
    Concat(ICommandSpec.CommonOptions);

  static FormatCommand() {
    DafnyOptions.RegisterLegacyBinding(Check, (options, value) => {
      options.FormatCheck = value;
    });
  }

  public Command Create() {
    var result = new Command("format", @"Format the dafny file in-place.
If no dafny file is provided, will look for every available Dafny file.
Use '--print -' to output the content of the formatted files instead of overwriting them.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Format = true;
    dafnyOptions.Compile = false;
  }
}
