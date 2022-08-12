using Dafny;

namespace Microsoft.Dafny;

class NoVerifyOption : BooleanOption {
  public static readonly NoVerifyOption Instance = new();
  public override string LongName => "noVerify";
  public override string ShortName => null;
  public override string Description => "missing";

  public override void PostProcess(DafnyOptions options) {
    options.Verify = !Get(options);
    base.PostProcess(options);
  }
}

class PrintOption : StringOption {
  public static readonly PrintOption Instance = new();
  public override object DefaultValue => null;
  public override string LongName => "print";
  public override string ShortName => null;
  public override string Description => "missing";
  public override bool CanBeUsedMultipleTimes => false;

  public override void PostProcess(DafnyOptions options) {
    options.DafnyPrintFile = Get(options);
    base.PostProcess(options);
  }
}

class TargetOption : StringOption {
  public static readonly TargetOption Instance = new();
  public override object DefaultValue => "cs";
  public override string LongName => "target";
  public override string ShortName => null;
  public override string Description => "missing";
  public override bool CanBeUsedMultipleTimes => false;
}