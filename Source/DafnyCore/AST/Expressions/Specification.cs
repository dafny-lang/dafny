#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class Specification<T> : NodeWithoutOrigin, IAttributeBearingDeclaration
  where T : Node {
  public List<T>? Expressions;

  public Specification() {
    Expressions = [];
    Attributes = null;
  }


  [SyntaxConstructor]
  public Specification(List<T>? expressions, Attributes? attributes) {
    Expressions = expressions;
    Attributes = attributes;
  }

  public Attributes? Attributes { get; set; }
  string IAttributeBearingDeclaration.WhatKind => "specification clause";

  public bool HasAttributes() {
    return Attributes != null;
  }

  public override IEnumerable<INode> Children => Expressions!;
  public override IEnumerable<INode> PreResolveChildren => Children;
}