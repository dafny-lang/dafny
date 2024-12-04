using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class DisplayExpression : Expression {
  public readonly List<Expression> Elements;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Elements));
  }

  protected DisplayExpression(Cloner cloner, DisplayExpression original) : base(cloner, original) {
    Elements = original.Elements.ConvertAll(cloner.CloneExpr);
  }

  public DisplayExpression(IOrigin tok, List<Expression> elements)
    : base(tok) {
    Contract.Requires(cce.NonNullElements(elements));
    Elements = elements;
  }

  public override IEnumerable<Expression> SubExpressions => Elements;
}