#nullable enable
namespace Microsoft.Dafny;

public abstract class NodeWithOrigin : Node {
  private IOrigin origin;

  protected NodeWithOrigin(Cloner cloner, NodeWithOrigin original)
    : this(cloner.Origin(original.Origin)) {
  }

  [SyntaxConstructor]
  protected NodeWithOrigin(IOrigin? origin) {
    this.origin = origin;
  }

  public void SetOrigin(IOrigin newOrigin) {
    origin = newOrigin;
  }

  public override IOrigin Origin => origin;
}