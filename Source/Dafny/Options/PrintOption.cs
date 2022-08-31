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
print Dafny program after parsing it
(use - as <file> to print to console)".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.DafnyPrintFile = Get(options);
    options.ExpandFilename(options.DafnyPrintFile, x => options.DafnyPrintFile = x, options.LogPrefix,
      options.FileTimestamp);
    return null;
  }
}

public class ResolvedPrintOption : StringOption {
  public static readonly ResolvedPrintOption Instance = new();
  public override object DefaultValue => null;
  public override bool Hidden => true;
  public override string LongName => "rprint";
  public override string ArgumentName => "file";
  public override string Category => "Overall reporting and printing";
  public override string Description => @"
print Dafny program after resolving it
(use - as <file> to print to console)".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.DafnyPrintResolvedFile = Get(options);
    options.ExpandFilename(options.DafnyPrintResolvedFile, x => options.DafnyPrintResolvedFile = x, options.LogPrefix,
      options.FileTimestamp);
    return null;
  }
}
