using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class UnaryExpr : Expression, ICanFormat {
  public readonly Expression E;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
  }

  public UnaryExpr(IOrigin tok, Expression e)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(e != null);
    this.E = e;
  }

  public UnaryExpr(Cloner cloner, UnaryExpr original) : base(cloner, original) {
    E = cloner.CloneExpr(original.E);
  }

  public override IEnumerable<Expression> SubExpressions {
    get { yield return E; }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentParensExpression(indentBefore, OwnedTokens);
  }
}