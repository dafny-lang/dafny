#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class OldExpr : Expression, ICloneable<OldExpr>, ICanFormat {
  [Peer]
  public Expression Expr;
  public string? At;
  [FilledInDuringResolution] public Label? AtLabel;  // after that, At==null iff AtLabel==null
  [FilledInDuringResolution] public bool Useless = false;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Expr != null);
  }

  public OldExpr(Cloner cloner, OldExpr original) : base(cloner, original) {
    Expr = cloner.CloneExpr(original.Expr);
    At = original.At;
    if (cloner.CloneResolvedFields) {
      AtLabel = original.AtLabel;
      Useless = original.Useless;
    }
  }

  public OldExpr Clone(Cloner cloner) {
    return new OldExpr(cloner, this);
  }

  [SyntaxConstructor]
  [Captured]
  public OldExpr(IOrigin origin, Expression expr, string? at = null)
    : base(origin) {
    Contract.Requires(origin != null);
    cce.Owner.AssignSame(this, expr);
    Expr = expr;
    At = at;
  }

  public override IEnumerable<Expression> SubExpressions {
    get { yield return Expr; }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }
}
