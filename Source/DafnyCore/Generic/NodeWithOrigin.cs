#nullable enable
using System.Linq;

namespace Microsoft.Dafny;

public abstract class NodeWithOrigin : Node {
  private IOrigin origin;

  protected NodeWithOrigin(Cloner cloner, NodeWithOrigin original)
    : this(cloner.Origin(original.Origin)) {
  }

  [SyntaxConstructor]
  protected NodeWithOrigin(IOrigin? origin) {
    this.origin = origin ?? Token.NoToken;
  }

  public void SetOrigin(IOrigin newOrigin) {
    origin = newOrigin;
  }

  public override IOrigin Origin => origin;


  private TokenRange? entireRange;

  public override TokenRange EntireRange {
    get {
      if (entireRange == null) {
        if (Origin.EntireRange == null) {
          var start = PreResolveChildren.FirstOrDefault()?.EntireRange.StartToken ?? Token.NoToken;
          var end = PreResolveChildren.LastOrDefault()?.EntireRange.EndToken ?? Token.NoToken;
          entireRange = new TokenRange(start, end);
        } else {
          entireRange = origin.EntireRange!;
        }
      }

      return entireRange;
    }
  }
}