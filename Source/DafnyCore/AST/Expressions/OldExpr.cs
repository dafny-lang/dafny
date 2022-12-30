using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class OldExpr : Expression {
  [Peer]
  public readonly Expression E;
  public readonly string/*?*/ At;
  [FilledInDuringResolution] public bool Useless = false;
  [FilledInDuringResolution] public Label/*?*/ AtLabel;  // after that, At==null iff AtLabel==null
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
  }

  [Captured]
  public OldExpr(IToken tok, Expression expr, string at = null)
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