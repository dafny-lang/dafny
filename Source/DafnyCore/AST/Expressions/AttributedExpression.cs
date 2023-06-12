using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class AttributedExpression : TokenNode, IAttributeBearingDeclaration {
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

  public override RangeToken RangeToken => E.RangeToken;

  public bool HasAttributes() {
    return Attributes != null;
  }

  public AttributedExpression(Expression e)
    : this(e, null) {
    Contract.Requires(e != null);
  }

  public AttributedExpression(Expression e, Attributes attrs) : this(e, null, attrs) {
  }

  public AttributedExpression(Expression e, AssertLabel/*?*/ label, Attributes attrs) {
    Contract.Requires(e != null);
    E = e;
    Label = label;
    Attributes = attrs;
    this.tok = e.Tok;
  }

  public void AddCustomizedErrorMessage(IToken tok, string s) {
    var args = new List<Expression>() { new StringLiteralExpr(tok, s, true) };
    IToken openBrace = tok;
    IToken closeBrace = new Token(tok.line, tok.col + 7 + s.Length + 1); // where 7 = length(":error ")
    this.Attributes = new UserSuppliedAttributes(tok, openBrace, closeBrace, args, this.Attributes);
  }

  public override IEnumerable<Node> Children =>
    (Attributes != null ? new List<Node>() { Attributes } : Enumerable.Empty<Node>()).Concat(
      new List<Node>() { E });

  public override IEnumerable<Node> PreResolveChildren => Children;
}