using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class MapDisplayExpr : Expression, ICanFormat, ICloneable<MapDisplayExpr> {
  public bool Finite;
  public List<ExpressionPair> Elements;

  public MapDisplayExpr(Cloner cloner, MapDisplayExpr original) : base(cloner, original) {
    Finite = original.Finite;
    Elements = original.Elements.Select(p => new ExpressionPair(cloner.CloneExpr(p.A), cloner.CloneExpr(p.B))).ToList();
  }

  public MapDisplayExpr(IOrigin tok, bool finite, List<ExpressionPair> elements)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(elements));
    Finite = finite;
    Elements = elements;
  }
  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var ep in Elements) {
        yield return ep.A;
        yield return ep.B;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }

  public MapDisplayExpr Clone(Cloner cloner) {
    return new MapDisplayExpr(cloner, this);
  }
}

public class ExpressionPair {
  public Expression A, B;
  public ExpressionPair(Expression a, Expression b) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    A = a;
    B = b;
  }
}