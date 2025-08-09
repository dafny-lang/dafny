using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// Represents an expression prefixed with ~, which is only valid for inexact fp64 literals.
/// This allows the parser to accept ~expr for any expression, and the resolver will
/// validate that it's only used on numeric literals.
/// </summary>
public class ApproximateExpr : ConcreteSyntaxExpression, ICloneable<ApproximateExpr> {
  public Expression Expr { get; }

  [SyntaxConstructor]
  public ApproximateExpr(IOrigin origin, Expression expr) : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(expr != null);
    Expr = expr;
  }

  public ApproximateExpr(Cloner cloner, ApproximateExpr original) : base(cloner, original) {
    Expr = cloner.CloneExpr(original.Expr);
  }

  public ApproximateExpr Clone(Cloner cloner) {
    return new ApproximateExpr(cloner, this);
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ResolvedExpression != null) {
        yield return ResolvedExpression;
      } else {
        // the expression hasn't yet been turned into a resolved expression, so use .Expr as the subexpression
        yield return Expr;
      }
    }
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return Expr;
    }
  }
}