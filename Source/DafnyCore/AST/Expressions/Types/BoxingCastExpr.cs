using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class BoxingCastExpr : Expression {  // a BoxingCastExpr is used only as a temporary placeholding during translation
  public readonly Expression E;
  public readonly Type FromType;
  public readonly Type ToType;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
    Contract.Invariant(FromType != null);
    Contract.Invariant(ToType != null);
  }

  public BoxingCastExpr(Expression e, Type fromType, Type toType)
    : base(e.Tok) {
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