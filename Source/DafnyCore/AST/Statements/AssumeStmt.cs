using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AssumeStmt : PredicateStmt, ICloneable<AssumeStmt> {
  public AssumeStmt Clone(Cloner cloner) {
    return new AssumeStmt(cloner, this);
  }

  public AssumeStmt(Cloner cloner, AssumeStmt original) : base(cloner, original) {
  }

  public AssumeStmt(IToken tok, IToken endTok, Expression expr, Attributes attrs)
    : base(tok, endTok, expr, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(expr != null);
  }
  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      yield return Expr;
    }
  }
}