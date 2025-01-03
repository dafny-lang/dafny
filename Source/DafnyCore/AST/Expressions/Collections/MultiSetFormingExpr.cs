using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class MultiSetFormingExpr : Expression, ICloneable<MultiSetFormingExpr> {
  [Peer]
  public readonly Expression E;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
  }

  public MultiSetFormingExpr(Cloner cloner, MultiSetFormingExpr original) : base(cloner, original) {
    E = cloner.CloneExpr(original.E);
  }

  [Captured]
  public MultiSetFormingExpr(IOrigin origin, Expression expr)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(expr != null);
    cce.Owner.AssignSame(this, expr);
    E = expr;
  }

  public override IEnumerable<Expression> SubExpressions {
    get { yield return E; }
  }

  public MultiSetFormingExpr Clone(Cloner cloner) {
    return new MultiSetFormingExpr(cloner, this);
  }
}