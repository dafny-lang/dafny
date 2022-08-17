namespace Microsoft.Dafny;

class DafnyVerifyOption : BooleanOption {
  public static readonly DafnyVerifyOption Instance = new();

  public override object DefaultValue => true;

  public override string PostProcess(DafnyOptions options) {
    options.DafnyVerify = Get(options);
    return null;
  }

  public override string LongName => "dafnyVerify";

  public override string ShortName => null;
  public override string Category => "Verification options";

  public override string Description => @"
0 - stop after typechecking
1 - continue on to translation, verification, and compilation".TrimStart();
}
