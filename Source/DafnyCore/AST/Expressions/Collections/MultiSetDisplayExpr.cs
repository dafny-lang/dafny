using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class MultiSetDisplayExpr : DisplayExpression, ICloneable<MultiSetDisplayExpr> {
  public MultiSetDisplayExpr(Cloner cloner, MultiSetDisplayExpr original) : base(cloner, original) {
  }

  public MultiSetDisplayExpr(IOrigin tok, List<Expression> elements) : base(tok, elements) {
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(elements));
  }

  public MultiSetDisplayExpr Clone(Cloner cloner) {
    return new MultiSetDisplayExpr(cloner, this);
  }
}