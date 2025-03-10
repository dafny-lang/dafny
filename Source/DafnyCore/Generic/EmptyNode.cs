using System.Collections.Generic;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public class EmptyNode() : NodeWithoutOrigin() {
  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();
  public override IEnumerable<INode> PreResolveChildren => Enumerable.Empty<Node>();
}