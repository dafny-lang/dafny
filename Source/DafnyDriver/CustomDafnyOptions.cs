using System.Linq;
using Dafny;

namespace Microsoft.Dafny;

class NoVerifyOption : BooleanOption {
  public static readonly NoVerifyOption Instance = new();
  public override string LongName => "noVerify";
  public override string ShortName => null;
  public override string Category => "Compilation options";
  public override string Description => "missing";

  public override string TypedPostProcess(DafnyOptions options, bool value) {
    options.Verify = !value;
    return base.TypedPostProcess(options, value);
  }
}

class BoogieOption : StringOption {
  public override object DefaultValue => null;
  public override string LongName => "boogie";
  public override string ShortName => "null";
  public override string ArgumentName => null;
  public override string Category => null;
  public override string Description => "arguments to boogie";

  public override string TypedPostProcess(DafnyOptions options, string value) {
    options.Parse(value.Split(" "));
    return base.TypedPostProcess(options, value);
  }
}
