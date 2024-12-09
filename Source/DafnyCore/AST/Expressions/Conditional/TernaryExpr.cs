using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class TernaryExpr : Expression, ICloneable<TernaryExpr> {
  public readonly Opcode Op;
  public readonly Expression E0;
  public readonly Expression E1;
  public readonly Expression E2;
  public enum Opcode { PrefixEqOp, PrefixNeqOp }

  public TernaryExpr(Cloner cloner, TernaryExpr original) : base(cloner, original) {
    Op = original.Op;
    E0 = cloner.CloneExpr(original.E0);
    E1 = cloner.CloneExpr(original.E1);
    E2 = cloner.CloneExpr(original.E2);
  }

  public TernaryExpr(IOrigin tok, Opcode op, Expression e0, Expression e1, Expression e2)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(e0 != null);
    Contract.Requires(e1 != null);
    Contract.Requires(e2 != null);
    Op = op;
    E0 = e0;
    E1 = e1;
    E2 = e2;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return E0;
      yield return E1;
      yield return E2;
    }
  }

  public TernaryExpr Clone(Cloner cloner) {
    return new TernaryExpr(cloner, this);
  }
}