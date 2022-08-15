namespace Microsoft.Dafny;

class CompileTargetOption : TargetOption {
  public new static readonly CompileTargetOption Instance = new();
  public override string LongName => "compileTarget";
}