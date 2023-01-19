using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public class AssumeStmt : PredicateStmt, ICloneable<AssumeStmt> {
  public AssumeStmt Clone(Cloner cloner) {
    return new AssumeStmt(cloner, this);
  }

  public AssumeStmt(Cloner cloner, AssumeStmt original) : base(cloner, original) {
  }

  public AssumeStmt(IToken tok, RangeToken rangeToken, Expression expr, Attributes attrs)
    : base(rangeToken, expr, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(rangeToken != null);
    Contract.Requires(expr != null);
  }
  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      yield return Expr;
    }
  }

  public override IEnumerable<AssumptionDescription> Assumptions() {
    yield return AssumptionDescription.AssumeStatement;
  }
}