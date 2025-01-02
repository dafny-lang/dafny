using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class MultiSetDisplayExpr : DisplayExpression, ICloneable<MultiSetDisplayExpr> {
  public MultiSetDisplayExpr(Cloner cloner, MultiSetDisplayExpr original) : base(cloner, original) {
  }

  public MultiSetDisplayExpr(IOrigin origin, List<Expression> elements) : base(origin, elements) {
    Contract.Requires(origin != null);
    Contract.Requires(cce.NonNullElements(elements));
  }

  public MultiSetDisplayExpr Clone(Cloner cloner) {
    return new MultiSetDisplayExpr(cloner, this);
  }
}