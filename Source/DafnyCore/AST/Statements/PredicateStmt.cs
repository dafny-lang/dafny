using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class PredicateStmt : Statement {
  public readonly Expression Expr;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Expr != null);
  }

  public PredicateStmt(IToken tok, IToken endTok, Expression expr, Attributes attrs)
    : base(tok, endTok, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(expr != null);
    this.Expr = expr;
  }

  public PredicateStmt(IToken tok, IToken endTok, Expression expr)
    : this(tok, endTok, expr, null) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(expr != null);
    this.Expr = expr;
  }
}