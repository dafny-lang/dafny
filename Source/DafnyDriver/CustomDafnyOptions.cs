using System.Linq;
using Dafny;

namespace Microsoft.Dafny;

class NoVerifyOption : BooleanOption {
  public static readonly NoVerifyOption Instance = new();
  public override string LongName => "noVerify";
  public override string ShortName => null;
  public override string Category => "Compilation options";
  public override string Description => "missing";

  public override string PostProcess(DafnyOptions options) {
    options.Verify = !Get(options);
    return null;
  }
}

class BoogieOption : StringOption {
  public static readonly BoogieOption Instance = new();
  public override object DefaultValue => null;
  public override string LongName => "boogie";
  public override string ShortName => "null";
  public override string ArgumentName => null;
  public override string Category => null;
  public override string Description => "arguments to boogie";

  public override string PostProcess(DafnyOptions options) {
    options.Parse(Get(options).Split(" "));
    return null;
  }
}
