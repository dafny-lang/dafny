using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class PredicateStmt : Statement, ICanResolve {
  public readonly Expression Expr;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Expr != null);
  }

  protected PredicateStmt(Cloner cloner, PredicateStmt original) : base(cloner, original) {
    Expr = cloner.CloneExpr(original.Expr);
  }

  protected PredicateStmt(RangeToken rangeToken, Expression expr, Attributes attrs)
    : base(rangeToken, attrs) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(expr != null);
    this.Expr = expr;
  }

  protected PredicateStmt(RangeToken rangeToken, Expression expr)
    : this(rangeToken, expr, null) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(expr != null);
    this.Expr = expr;
  }

  public override void Resolve(Resolver resolver, ResolutionContext context) {
    base.Resolve(resolver, context);
    resolver.ResolveExpression(Expr, context);
    Contract.Assert(Expr.Type != null); // follows from postcondition of ResolveExpression
    resolver.ConstrainTypeExprBool(Expr, "condition is expected to be of type bool, but is {0}");
  }
}