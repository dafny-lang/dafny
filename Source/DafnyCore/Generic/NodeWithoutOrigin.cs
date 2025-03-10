#nullable enable
using System.Linq;

namespace Microsoft.Dafny;

public abstract class NodeWithoutOrigin : Node {
  private IOrigin? origin;

  public override IOrigin Origin => origin ??= new SourceOrigin(EntireRange);

  private TokenRange? entireRange;

  public override TokenRange EntireRange {
    get {
      if (entireRange == null) {
        var start = PreResolveChildren.FirstOrDefault()?.EntireRange.StartToken ?? Token.NoToken;
        var end = PreResolveChildren.LastOrDefault()?.EntireRange.EndToken ?? Token.NoToken;
        entireRange = new TokenRange(start, end);
      }

      return entireRange;
    }
  }
}