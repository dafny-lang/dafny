using System.Linq;

namespace Microsoft.Dafny;

class BoogieOption : StringOption {
  public static readonly BoogieOption Instance = new();
  public override object DefaultValue => null;
  public override string LongName => "boogie";
  public override string ArgumentName => "arguments";
  public override string Category => null;
  public override string Description => "Specify arguments that are passed to Boogie, a tool used to verify Dafny programs.";

  public override string PostProcess(DafnyOptions options) {
    var boogieOptions = Get(options);
    if (boogieOptions != null) {
      options.Parse(boogieOptions.Split(" "));
    }
    return null;
  }
}
