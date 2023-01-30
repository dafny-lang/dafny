using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ExpectStmt : PredicateStmt, ICloneable<ExpectStmt> {
  public Expression Message;

  public ExpectStmt Clone(Cloner cloner) {
    return new ExpectStmt(cloner, this);
  }

  public override IToken Tok => StartToken == Expr.StartToken ? Expr.Tok : base.Tok; // TODO move up to PredicateStmt?

  public ExpectStmt(Cloner cloner, ExpectStmt original) : base(cloner, original) {
    Message = cloner.CloneExpr(original.Message);
  }

  public ExpectStmt(RangeToken rangeToken, Expression expr, Expression message, Attributes attrs)
    : base(rangeToken, expr, attrs) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(expr != null);
    this.Message = message;
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      yield return Expr;
      if (Message != null) {
        yield return Message;
      }
    }
  }
}