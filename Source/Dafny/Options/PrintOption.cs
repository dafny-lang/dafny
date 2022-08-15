namespace Microsoft.Dafny;

public class PrintOption : StringOption {
  public static readonly PrintOption Instance = new();
  public override object GetDefaultValue(DafnyOptions options) => null;

  public override string LongName => "print";
  public override string ShortName => null;
  public override string Category => "Overall reporting and printing";
  public override string Description => @"
print Dafny program after parsing it
(use - as <file> to print to console)".TrimStart();
  public override bool CanBeUsedMultipleTimes => false;

  public override void PostProcess(DafnyOptions options) {
    options.DafnyPrintFile = Get(options);
    options.ExpandFilename(options.DafnyPrintFile, x => options.DafnyPrintFile = x, options.LogPrefix,
      options.FileTimestamp);
    base.PostProcess(options);
  }
}