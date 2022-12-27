using System.CommandLine;
using System.IO;

namespace Microsoft.Dafny;

public class DeveloperOptionBag {

  public static readonly Option<bool> SpillTranslation = new("--spill-translation",
    @"In case the Dafny source code is translated to another language, emit that translation.") {
    IsHidden = true
  };

  public static readonly Option<bool> UseBaseFileName = new("--useBaseNameForFileName",
    "When parsing use basename of file for tokens instead of the path supplied on the command line") {
    IsHidden = true
  };

  public static readonly Option<string> BoogiePrint = new("--bprint",
  @"
Print Boogie program translated from Dafny
(use - as <file> to print to console)".TrimStart()) {
    IsHidden = true,
    ArgumentHelpName = "file"
  };

  public static readonly Option<string> Print = new("--print", @"
Print Dafny program after parsing it.
(Use - as <file> to print to console.)".TrimStart()) {
    IsHidden = true,
    ArgumentHelpName = "file"
  };

  public static readonly Option<string> ResolvedPrint = new("--rprint", @"
Print Dafny program after resolving it.
(use - as <file> to print to console.)".TrimStart()) {
    IsHidden = true,
    ArgumentHelpName = "file"
  };

  static DeveloperOptionBag() {
    DafnyOptions.RegisterLegacyBinding(SpillTranslation, (o, f) => o.SpillTargetCode = f ? 1U : 0U);

    DafnyOptions.RegisterLegacyBinding(ResolvedPrint, (options, value) => {
      options.DafnyPrintResolvedFile = value;
      options.ExpandFilename(options.DafnyPrintResolvedFile, x => options.DafnyPrintResolvedFile = x, options.LogPrefix,
        options.FileTimestamp);
    });

    DafnyOptions.RegisterLegacyBinding(Print, (options, value) => {
      options.DafnyPrintFile = value;
      options.ExpandFilename(options.DafnyPrintFile, x => options.DafnyPrintFile = x, options.LogPrefix,
        options.FileTimestamp);
    });

    DafnyOptions.RegisterLegacyBinding(UseBaseFileName, (o, f) => o.UseBaseNameForFileName = f);
    DafnyOptions.RegisterLegacyBinding(BoogiePrint, (options, f) => {
      options.PrintFile = f;
      options.ExpandFilename(options.PrintFile, x => options.PrintFile = x, options.LogPrefix,
        options.FileTimestamp);
    });
  }
}
