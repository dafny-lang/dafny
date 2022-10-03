namespace Microsoft.Dafny;

public class ResolvedPrintOption : StringOption, ILegacyOption {
  public static readonly ResolvedPrintOption Instance = new();
  public override object DefaultValue => null;
  public override bool Hidden => true;
  public override string LongName => "rprint";
  public override string ArgumentName => "file";
  public string Category => "Overall reporting and printing";
  public string LegacyName => LongName;

  public override string Description => @"
Print Dafny program after resolving it. (use - as <file> to print
to console.)".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.DafnyPrintResolvedFile = Get(options);
    options.ExpandFilename(options.DafnyPrintResolvedFile, x => options.DafnyPrintResolvedFile = x, options.LogPrefix,
      options.FileTimestamp);
    return null;
  }
}
