using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ExpectStmt : PredicateStmt, ICloneable<ExpectStmt> {
  public Expression Message;

  public ExpectStmt Clone(Cloner cloner) {
    return new ExpectStmt(cloner, this);
  }

  public ExpectStmt(Cloner cloner, ExpectStmt original) : base(cloner, original) {
    Message = cloner.CloneExpr(original.Message);
  }

  public ExpectStmt(IToken tok, IToken endTok, Expression expr, Expression message, Attributes attrs)
    : base(tok, endTok, expr, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
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