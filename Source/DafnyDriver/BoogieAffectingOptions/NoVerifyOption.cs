namespace Microsoft.Dafny;

class NoVerifyOption : BooleanOption {
  public static readonly NoVerifyOption Instance = new();
  public override string LongName => "no-verify";
  public override string ShortName => null;
  public override string Description => "Skip verification";

  public override string PostProcess(DafnyOptions options) {
    options.Verify = !Get(options);
    return null;
  }
}
