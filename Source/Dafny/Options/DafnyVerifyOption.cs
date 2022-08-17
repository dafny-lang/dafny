namespace Microsoft.Dafny;

class DafnyVerifyOption : BooleanOption {
  public static readonly DafnyVerifyOption Instance = new();
  public override object GetDefaultValue(DafnyOptions options) {
    return 1;
  }

  public override void TypedPostProcess(DafnyOptions options, bool value) {
    options.DafnyVerify = value;
    base.PostProcess(options, value);
  }

  public override string LongName => "dafnyVerify";

  public override string ShortName => null;
  public override string Category => "Verification options";

  public override string Description => @"
0 - stop after typechecking
1 - continue on to translation, verification, and compilation".TrimStart();
}
