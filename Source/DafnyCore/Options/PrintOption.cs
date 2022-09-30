namespace Microsoft.Dafny;

public class PrintOption : StringOption, ILegacyOption {
  public static readonly PrintOption Instance = new();
  public override object DefaultValue => null;
  public override bool Hidden => true;
  public override string LongName => "print";
  public string LegacyName => "dprint";
  public override string ArgumentName => "file";
  public string Category => "Overall reporting and printing";
  public override string Description => @"
Print Dafny program after parsing it. (Use - as <file> to print
to console.)".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.DafnyPrintFile = Get(options);
    options.ExpandFilename(options.DafnyPrintFile, x => options.DafnyPrintFile = x, options.LogPrefix,
      options.FileTimestamp);
    return null;
  }
}
