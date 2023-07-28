using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class Specification<T> : TokenNode, IAttributeBearingDeclaration
  where T : Node {
  public readonly List<T> Expressions;

  [ContractInvariantMethod]
  private void ObjectInvariant() {
    Contract.Invariant(Expressions == null || cce.NonNullElements<T>(Expressions));
  }

  public Specification(List<T> exprs, Attributes attrs) {
    Contract.Requires(exprs == null || cce.NonNullElements<T>(exprs));
    Expressions = exprs;
    Attributes = attrs;
  }

  public Attributes Attributes { get; set; }

  public bool HasAttributes() {
    return Attributes != null;
  }

  public override IEnumerable<Node> Children => Expressions;
  public override IEnumerable<Node> PreResolveChildren => Children;
}