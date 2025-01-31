using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class Specification<T> : NodeWithComputedRange, IAttributeBearingDeclaration
  where T : Node {
  public readonly List<T> Expressions;

  [ContractInvariantMethod]
  private void ObjectInvariant() {
    Contract.Invariant(Expressions == null || cce.NonNullElements<T>(Expressions));
  }

  public Specification() {
    Expressions = new List<T>();
    Attributes = null;
  }

  public Specification(List<T> expressions, Attributes attributes) {
    Contract.Requires(expressions == null || cce.NonNullElements<T>(expressions));
    Expressions = expressions;
    Attributes = attributes;
  }

  public Attributes Attributes { get; set; }
  string IAttributeBearingDeclaration.WhatKind => "specification clause";

  public bool HasAttributes() {
    return Attributes != null;
  }

  public override IEnumerable<INode> Children => Expressions;
  public override IEnumerable<INode> PreResolveChildren => Children;
}