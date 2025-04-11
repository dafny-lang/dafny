using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class OldExpr : Expression, ICloneable<OldExpr>, ICanFormat {
  [Peer]
  public Expression E;
  public string/*?*/ At;
  [FilledInDuringResolution] public Label/*?*/ AtLabel;  // after that, At==null iff AtLabel==null
  [FilledInDuringResolution] public bool Useless = false;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
  }

  public OldExpr(Cloner cloner, OldExpr original) : base(cloner, original) {
    E = cloner.CloneExpr(original.E);
    At = original.At;
    if (cloner.CloneResolvedFields) {
      AtLabel = original.AtLabel;
      Useless = original.Useless;
    }
  }

  public OldExpr Clone(Cloner cloner) {
    return new OldExpr(cloner, this);
  }

  [Captured]
  public OldExpr(IOrigin origin, Expression expr, string at = null)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(expr != null);
    cce.Owner.AssignSame(this, expr);
    E = expr;
    At = at;
  }

  public override IEnumerable<Expression> SubExpressions {
    get { yield return E; }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }
}
