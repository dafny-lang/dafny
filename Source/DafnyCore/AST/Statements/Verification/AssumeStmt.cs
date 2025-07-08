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

  public AssumeStmt(IOrigin origin, Expression expr, Attributes attributes)
    : base(origin, expr, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(expr != null);
  }
  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      yield return Expr;
    }
  }

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    yield return new Assumption(decl, Origin, AssumptionDescription.AssumeStatement(
      Attributes.Contains(Attributes, Attributes.AxiomAttributeName)));
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentAssertLikeStatement(this, indentBefore);
  }

  public override void GenResolve(INewOrOldResolver resolver, ResolutionContext context) {
    base.GenResolve(resolver, context);

    if (!resolver.Options.Get(CommonOptionBag.AllowAxioms) && !this.IsExplicitAxiom()) {
      resolver.Reporter.Warning(MessageSource.Verifier, ResolutionErrors.ErrorId.r_assume_statement_without_axiom, Origin, "assume statement has no {:axiom} annotation");
    }
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext,
    string proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    IsGhost = true;
  }
}
