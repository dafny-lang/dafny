using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class EmptyNode : Node {
  public override IOrigin Origin { get; } = new Token();
  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();
  public override IEnumerable<INode> PreResolveChildren => Enumerable.Empty<Node>();
}