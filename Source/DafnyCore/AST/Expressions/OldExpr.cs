using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class OldExpr : Expression, ICloneable<OldExpr> {
  [Peer]
  public readonly Expression E;
  public readonly string/*?*/ At;
  [FilledInDuringResolution] public Label/*?*/ AtLabel;  // after that, At==null iff AtLabel==null
  [FilledInDuringResolution] public bool Useless = false;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
  }

  public OldExpr Clone(Cloner cloner) {
    var result = new OldExpr(cloner.Tok(tok), cloner.CloneExpr(E), At);
    if (cloner.CloneResolvedFields) {
      result.AtLabel = AtLabel;
      result.Useless = Useless;
    }
    return result;
  }

  [Captured]
  public OldExpr(RangeToken tok, Expression expr, string at = null)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(expr != null);
    cce.Owner.AssignSame(this, expr);
    E = expr;
    At = at;
  }

  public override IEnumerable<Expression> SubExpressions {
    get { yield return E; }
  }
}