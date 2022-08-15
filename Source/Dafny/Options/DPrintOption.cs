namespace Microsoft.Dafny;

class DPrintOption : PrintOption {
  public new static readonly DPrintOption Instance = new();
  public override string LongName => "dprint";
}