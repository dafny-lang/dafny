namespace Microsoft.Dafny;

class DPrintOption : PrintOption {
  public new static readonly DPrintOption Instance = new();
  public override string LongName => "dprint";
}

public class PrintOption : StringOption {
  public static readonly PrintOption Instance = new();
  public override object DefaultValue => null;
  public override bool Hidden => true;
  public override string LongName => "print";
  public override string ArgumentName => "file";
  public override string Category => "Overall reporting and printing";
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
