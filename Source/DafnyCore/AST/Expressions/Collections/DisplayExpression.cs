#nullable enable

using System.Collections.Generic;

namespace Microsoft.Dafny;

public abstract class DisplayExpression : Expression {
  public List<Expression> Elements;

  protected DisplayExpression(Cloner cloner, DisplayExpression original) : base(cloner, original) {
    Elements = original.Elements.ConvertAll(cloner.CloneExpr);
  }

  [SyntaxConstructor]
  public DisplayExpression(IOrigin origin, List<Expression> elements)
    : base(origin) {
    Elements = elements;
  }

  public override IEnumerable<Expression> SubExpressions => Elements;
}