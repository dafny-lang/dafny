using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public class AssumeStmt : PredicateStmt, ICloneable<AssumeStmt>, ICanFormat {
  public AssumeStmt Clone(Cloner cloner) {
    return new AssumeStmt(cloner, this);
  }

  public AssumeStmt(Cloner cloner, AssumeStmt original) : base(cloner, original) {
  }

  public AssumeStmt(RangeToken rangeToken, Expression expr, Attributes attrs)
    : base(rangeToken, expr, attrs) {
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

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentAssertLikeStatement(this, indentBefore);
  }

  public override void Resolve(Resolver resolver, ResolutionContext context) {
    base.Resolve(resolver, context);

    if (!resolver.Options.Get(CommonOptionBag.AllowAxioms) && !this.IsExplicitAxiom()) {
      resolver.Reporter.Warning(MessageSource.Resolver, ErrorDetail.ErrorID.None, Tok, "Assume statement has no {:axiom} annotation");
    }
  }
}