namespace Microsoft.Dafny;

public class BoogiePrintOption : StringOption {
  public static readonly BoogiePrintOption Instance = new();
  public override object DefaultValue => null;
  public override bool Hidden => true;
  public override string LongName => "bprint";
  public override string ArgumentName => "file";
  public override string Description => @"
print Boogie program translated from Dafny
(use - as <file> to print to console)".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.PrintFile = Get(options);
    options.ExpandFilename(options.PrintFile, x => options.PrintFile = x, options.LogPrefix,
      options.FileTimestamp);
    return null;
  }
}