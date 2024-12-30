using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class LetOrFailExpr : ConcreteSyntaxExpression, ICloneable<LetOrFailExpr>, ICanFormat {
  public readonly CasePattern<BoundVar>/*?*/ Lhs; // null means void-error handling: ":- E; F", non-null means "var pat :- E; F"
  public readonly Expression Rhs;
  public readonly Expression Body;

  public LetOrFailExpr(IOrigin tok, CasePattern<BoundVar>/*?*/ lhs, Expression rhs, Expression body) : base(tok) {
    Lhs = lhs;
    Rhs = rhs;
    Body = body;
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return Rhs;
      yield return Body;
    }
  }

  public LetOrFailExpr Clone(Cloner cloner) {
    return new LetOrFailExpr(cloner, this);
  }

  public LetOrFailExpr(Cloner cloner, LetOrFailExpr original) : base(cloner, original) {
    Lhs = original.Lhs == null ? null : cloner.CloneCasePattern(original.Lhs);
    Rhs = cloner.CloneExpr(original.Rhs);
    Body = cloner.CloneExpr(original.Body);
  }

  public override IEnumerable<INode> Children =>
    (Lhs != null ?
      new List<Node> { Lhs } : Enumerable.Empty<Node>()).Concat(base.Children);

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentVarDeclStmt(indentBefore, OwnedTokens, Lhs == null, true);
  }
}