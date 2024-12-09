using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class AttributedExpression : RangeNode, IAttributeBearingDeclaration {
  public readonly Expression E;
  public readonly AssertLabel/*?*/ Label;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
  }

  private Attributes attributes;
  public Attributes Attributes {
    get {
      return attributes;
    }
    set {
      attributes = value;
    }
  }

  string IAttributeBearingDeclaration.WhatKind => "expression";

  public bool HasAttributes() {
    return Attributes != null;
  }

  public AttributedExpression(IOrigin origin, Expression e)
    : this(origin, e, null) {
    Contract.Requires(e != null);
  }

  public AttributedExpression(IOrigin origin, Expression e, Attributes attrs) : this(origin, e, null, attrs) {
  }

  public AttributedExpression(IOrigin origin, Expression e, AssertLabel/*?*/ label, Attributes attrs) 
   : base(origin) {
    Contract.Requires(e != null);
    E = e;
    Label = label;
    Attributes = attrs;
  }

  public void AddCustomizedErrorMessage(IOrigin tok, string s) {
    var args = new List<Expression>() { new StringLiteralExpr(tok, s, true) };
    IOrigin openBrace = tok;
    IOrigin closeBrace = new Token(tok.line, tok.col + 7 + s.Length + 1); // where 7 = length(":error ")
    this.Attributes = new UserSuppliedAttributes(tok, openBrace, closeBrace, args, this.Attributes);
  }

  public override IEnumerable<INode> Children =>
    Attributes.AsEnumerable().Concat<Node>(
      new List<Node>() { E });

  public override IEnumerable<INode> PreResolveChildren => Children;
}