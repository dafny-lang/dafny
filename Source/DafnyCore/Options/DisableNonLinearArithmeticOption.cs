namespace Microsoft.Dafny;

class DisableNonLinearArithmeticOption : BooleanOption {
  public static readonly DisableNonLinearArithmeticOption Instance = new();
  public override string LongName => "disable-nonlinear-arithmetic";

  public override string Description => @"
(experimental, will be replaced in the future)
Reduce Dafny's knowledge of non-linear arithmetic (*,/,%).
  
Results in more manual work, but also produces more predictable behavior.".TrimStart();
  public override string PostProcess(DafnyOptions options) {
    options.DisableNLarith = Get(options);
    return null;
  }
}
