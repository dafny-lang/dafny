#nullable enable
using System.Linq;

namespace Microsoft.Dafny;

public abstract class NodeWithOrigin : Node {
  private IOrigin origin;

  protected NodeWithOrigin(Cloner cloner, NodeWithOrigin original)
    : this(cloner.Origin(original.Origin)) {
  }

  [SyntaxConstructor]
  protected NodeWithOrigin(IOrigin origin) {
    this.origin = origin;
  }

  public void SetOrigin(IOrigin newOrigin) {
    origin = newOrigin;
  }

  public override IOrigin Origin => origin;


  private Token? startToken;
  private Token? endToken;

  public override Token StartToken {
    get {
      return startToken ??= Origin.StartToken ?? PreResolveChildren.First().StartToken;
    }
  }

  public override Token EndToken {
    get { return endToken ??= Origin.EndToken ?? PreResolveChildren.Last().EndToken; }
  }
}