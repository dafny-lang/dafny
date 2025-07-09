using System.Collections.Generic;

namespace Microsoft.Dafny;

public class ParensExpression : ConcreteSyntaxExpression, ICanFormat, ICloneable<ParensExpression> {
  public Expression E;

  [SyntaxConstructor]
  public ParensExpression(IOrigin origin, Expression e)
    : base(origin) {
    E = e;
  }

  protected ParensExpression(Cloner cloner, ParensExpression original) : base(cloner, original) {
    E = cloner.CloneExpr(original.E);
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ResolvedExpression == null) {
        yield return E;
      } else {
        yield return ResolvedExpression;
      }
    }
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return E;
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }

  public ParensExpression Clone(Cloner cloner) {
    return new ParensExpression(cloner, this);
  }
}