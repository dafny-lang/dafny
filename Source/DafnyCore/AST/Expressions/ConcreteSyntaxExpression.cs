using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// This class represents a piece of concrete syntax in the parse tree.  During resolution,
/// it gets "replaced" by the expression in "ResolvedExpression".
/// </summary>
public abstract class ConcreteSyntaxExpression : Expression {
  protected ConcreteSyntaxExpression(Cloner cloner, ConcreteSyntaxExpression original) : base(cloner, original) {
    if (cloner.CloneResolvedFields && original.ResolvedExpression != null) {
      ResolvedExpression = cloner.CloneExpr(original.ResolvedExpression);
    }
  }

  [FilledInDuringResolution]
  private Expression resolvedExpression;

  public Expression ResolvedExpression {
    get => resolvedExpression;
    set {
      resolvedExpression = value;
      if (RangeOrigin != null && resolvedExpression != null) {
        resolvedExpression.Origin = RangeOrigin;
      }
    }
  }  // after resolution, manipulation of "this" should proceed as with manipulating "this.ResolvedExpression"

  public ConcreteSyntaxExpression(IOrigin tok)
    : base(tok) {
  }
  public override IEnumerable<INode> Children => ResolvedExpression == null ? Array.Empty<Node>() : new[] { ResolvedExpression };
  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ResolvedExpression != null) {
        yield return ResolvedExpression;
      }
    }
  }

  public override IEnumerable<Expression> TerminalExpressions {
    get {
      foreach (var e in ResolvedExpression.TerminalExpressions) {
        yield return e;
      }
    }
  }

  public virtual IEnumerable<Expression> PreResolveSubExpressions => Enumerable.Empty<Expression>();
  public override IEnumerable<INode> PreResolveChildren => PreResolveSubExpressions;

  public override IEnumerable<Type> ComponentTypes => ResolvedExpression.ComponentTypes;
}