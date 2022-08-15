using System.Linq;
using Dafny;

namespace Microsoft.Dafny;

class NoVerifyOption : BooleanOption {
  public static readonly NoVerifyOption Instance = new();
  public override string LongName => "noVerify";
  public override string ShortName => null;
  public override string Category => "Compilation options";
  public override string Description => "missing";

  public override void PostProcess(DafnyOptions options) {
    options.Verify = !Get(options);
    base.PostProcess(options);
  }
}
