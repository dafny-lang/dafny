using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class PredicateStmt : Statement {
  public readonly Expression Expr;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Expr != null);
  }

  protected PredicateStmt(Cloner cloner, PredicateStmt original) : base(cloner, original) {
    Expr = cloner.CloneExpr(original.Expr);
  }

  protected PredicateStmt(IToken tok, RangeToken rangeToken, Expression expr, Attributes attrs)
    : base(tok, rangeToken, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(rangeToken != null);
    Contract.Requires(expr != null);
    this.Expr = expr;
  }

  protected PredicateStmt(IToken tok, RangeToken rangeToken, Expression expr)
    : this(tok, rangeToken, expr, null) {
    Contract.Requires(tok != null);
    Contract.Requires(rangeToken != null);
    Contract.Requires(expr != null);
    this.Expr = expr;
  }
}