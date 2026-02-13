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

  /// <summary>
  /// // after resolution, manipulation of "this" should proceed as with manipulating "this.ResolvedExpression"
  /// </summary>
  [FilledInDuringResolution]
  public Expression ResolvedExpression { get; set; }

  [SyntaxConstructor]
  protected ConcreteSyntaxExpression(IOrigin origin)
    : base(origin) {
  }
  public override IEnumerable<INode> Children => ResolvedExpression == null ? Array.Empty<Node>() : [ResolvedExpression
  ];
  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ResolvedExpression != null) {
        yield return ResolvedExpression;
      }
    }
  }

  public override IEnumerable<Expression> TerminalExpressions {
    get {
      if (ResolvedExpression != null) {
        foreach (var e in ResolvedExpression.TerminalExpressions) {
          yield return e;
        }
      }
    }
  }

  public virtual IEnumerable<Expression> PreResolveSubExpressions => [];
  public override IEnumerable<INode> PreResolveChildren => PreResolveSubExpressions;

  public override IEnumerable<Type> ComponentTypes => ResolvedExpression.ComponentTypes;
}