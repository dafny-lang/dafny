using System.CommandLine;
using System.IO;
using DafnyCore;

namespace Microsoft.Dafny;

public class DeveloperOptionBag {

  public static readonly Option<string> BoogiePrint = new("--bprint",
  @"
Print Boogie program translated from Dafny
(use - as <file> to print to console)".TrimStart()) {
    IsHidden = true,
    ArgumentHelpName = "file",
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
    ArgumentHelpName = "file",
  };

  public static readonly Option<bool> Bootstrapping = new("--bootstrapping", @"
(internal, may be removed in the future)
Indicates the Dafny source is part of the Dafny implementation itself,
enabling necessary special handling.".TrimStart()) {
    IsHidden = true,
  };

  static DeveloperOptionBag() {

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

    DafnyOptions.RegisterLegacyBinding(BoogiePrint, (options, f) => {
      options.PrintFile = f;
      options.ExpandFilename(options.PrintFile, x => options.PrintFile = x, options.LogPrefix,
        options.FileTimestamp);
    });

    DooFile.RegisterNoChecksNeeded(
      BoogiePrint,
      Print,
      ResolvedPrint,
      Bootstrapping
    );
  }
}
