using Microsoft.Boogie;

namespace Microsoft.Dafny;

class PrintModeOption : CommandLineOption<DafnyOptions.PrintModes> {
  public static readonly PrintModeOption Instance = new();
  public override bool Hidden => true;

  public override object DefaultValue => DafnyOptions.PrintModes.Everything;
  public override string LongName => "printMode";
  public override string ShortName => null;
  public override string ArgumentName => "Everything|DllEmbed|NoIncludes|NoGhost";
  public override string Category => "Overall reporting and printing";

  public override string Description => @"
Everything is the default.
DllEmbed prints the source that will be included in a compiled dll.
NoIncludes disables printing of {{:verify false}} methods incorporated via the
include mechanism, as well as datatypes and fields included from other files.
NoGhost disables printing of functions, ghost methods, and proof statements in
implementation methods.  It also disables anything NoIncludes disables.";
  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    if (ps.ConfirmArgumentCount(1)) {
      if (ps.args[ps.i].Equals("Everything")) {
        Set(options, DafnyOptions.PrintModes.Everything);
      } else if (ps.args[ps.i].Equals("NoIncludes")) {
        Set(options, DafnyOptions.PrintModes.NoIncludes);
      } else if (ps.args[ps.i].Equals("NoGhost")) {
        Set(options, DafnyOptions.PrintModes.NoGhost);
      } else if (ps.args[ps.i].Equals("DllEmbed")) {
        Set(options, DafnyOptions.PrintModes.DllEmbed);
      } else {
        InvalidArgumentError(LongName, ps);
      }
    }
  }
  public override string PostProcess(DafnyOptions options) {
    options.PrintMode = Get(options);
    return null;
  }
}