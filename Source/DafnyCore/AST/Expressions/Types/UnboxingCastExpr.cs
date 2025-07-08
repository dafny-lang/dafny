using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class UnboxingCastExpr : Expression {  // an UnboxingCastExpr is used only as a temporary placeholding during translation
  public Expression E;
  public Type FromType;
  public Type ToType;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
    Contract.Invariant(FromType != null);
    Contract.Invariant(ToType != null);
  }

  public UnboxingCastExpr(Expression e, Type fromType, Type toType)
    : base(e.Origin) {
    Contract.Requires(e != null);
    Contract.Requires(fromType != null);
    Contract.Requires(toType != null);

    E = e;
    FromType = fromType;
    ToType = toType;
  }

  public override IEnumerable<Expression> SubExpressions {
    get { yield return E; }
  }
}