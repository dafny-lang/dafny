using System.Linq;
using Dafny;

namespace Microsoft.Dafny;

class BoogieOption : StringOption {
  public static readonly BoogieOption Instance = new();
  public override object DefaultValue => null;
  public override string LongName => "boogie";
  public override string ArgumentName => null;
  public override string Category => null;
  public override string Description => "arguments to boogie";

  public override string PostProcess(DafnyOptions options) {
    var boogieOptions = Get(options);
    if (boogieOptions != null) {
      options.Parse(boogieOptions.Split(" "));
    }
    return null;
  }
}
