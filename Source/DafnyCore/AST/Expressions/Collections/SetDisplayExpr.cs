using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class SetDisplayExpr : DisplayExpression, ICanFormat, ICloneable<SetDisplayExpr> {
  public bool Finite;
  public SetDisplayExpr(IOrigin origin, bool finite, List<Expression> elements)
    : base(origin, elements) {
    Contract.Requires(origin != null);
    Contract.Requires(cce.NonNullElements(elements));
    Finite = finite;
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }

  public SetDisplayExpr(Cloner cloner, SetDisplayExpr original) : base(cloner, original) {
    Finite = original.Finite;
  }

  public SetDisplayExpr Clone(Cloner cloner) {
    return new SetDisplayExpr(cloner, this);
  }
}