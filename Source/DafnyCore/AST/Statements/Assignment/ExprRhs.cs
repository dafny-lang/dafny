using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ExprRhs : AssignmentRhs, ICloneable<ExprRhs> {
  public readonly Expression Expr;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Expr != null);
  }
  public ExprRhs Clone(Cloner cloner) {
    return new ExprRhs(cloner, this);
  }

  public ExprRhs(Cloner cloner, ExprRhs original) : base(cloner, original) {
    Expr = cloner.CloneExpr(original.Expr);
  }

  public ExprRhs(Expression expr, Attributes attrs = null)
    : base(expr.Tok, attrs) {
    Contract.Requires(expr != null);
    Expr = expr;
  }
  public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      yield return Expr;
    }
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      foreach (var expr in base.PreResolveSubExpressions) {
        yield return expr;
      }

      yield return Expr;
    }
  }

  public override IEnumerable<INode> Children => new[] { Expr };
  public override IEnumerable<INode> PreResolveChildren => PreResolveSubExpressions;
}