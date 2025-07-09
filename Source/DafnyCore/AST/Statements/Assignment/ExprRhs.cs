#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ExprRhs : AssignmentRhs, ICloneable<ExprRhs> {
  public Expression Expr;
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

  [SyntaxConstructor]
  public ExprRhs(IOrigin origin, Expression expr, Attributes? attributes = null)
    : base(origin, attributes) {
    Expr = expr;
  }

  public ExprRhs(Expression expr, Attributes? attrs = null)
    : base(expr.Origin, attrs) {
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