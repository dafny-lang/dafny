namespace Microsoft.Dafny;

public class PrintOption : StringOption {
  public static readonly PrintOption Instance = new();
  public override object DefaultValue => null;

  public override string LongName => "print";
  public override string ShortName => null;
  public override string ArgumentName => "file";
  public override string Category => "Overall reporting and printing";
  public override string Description => @"
print Dafny program after parsing it
(use - as <file> to print to console)".TrimStart();

  public override string TypedPostProcess(DafnyOptions options, string value) {
    options.DafnyPrintFile = value;
    options.ExpandFilename(options.DafnyPrintFile, x => options.DafnyPrintFile = x, options.LogPrefix,
      options.FileTimestamp);
    return base.TypedPostProcess(options, value);
  }
}
