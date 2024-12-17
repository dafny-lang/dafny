using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class PredicateStmt : Statement, ICanResolveNewAndOld {
  public readonly Expression Expr;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Expr != null);
  }

  protected PredicateStmt(Cloner cloner, PredicateStmt original) : base(cloner, original) {
    Expr = cloner.CloneExpr(original.Expr);
  }

  protected PredicateStmt(IOrigin rangeOrigin, Expression expr, Attributes attrs)
    : base(rangeOrigin, attrs) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(expr != null);
    this.Expr = expr;
  }

  protected PredicateStmt(IOrigin rangeOrigin, Expression expr)
    : this(rangeOrigin, expr, null) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(expr != null);
    this.Expr = expr;
  }

  public override void GenResolve(INewOrOldResolver resolver, ResolutionContext context) {
    base.GenResolve(resolver, context);
    resolver.ResolveExpression(Expr, context);// follows from postcondition of ResolveExpression
    resolver.ConstrainTypeExprBool(Expr, "condition is expected to be of type bool, but is {0}");
  }
}