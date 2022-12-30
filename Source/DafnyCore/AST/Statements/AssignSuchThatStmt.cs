using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class AssignSuchThatStmt : ConcreteUpdateStatement {
  public readonly Expression Expr;
  public readonly AttributedToken AssumeToken;

  [FilledInDuringResolution] public List<ComprehensionExpr.BoundedPool> Bounds;  // null for a ghost statement
  // invariant Bounds == null || Bounds.Count == BoundVars.Count;
  [FilledInDuringResolution] public List<IVariable> MissingBounds;  // remains "null" if bounds can be found
  // invariant Bounds == null || MissingBounds == null;
  public class WiggleWaggleBound : ComprehensionExpr.BoundedPool {
    public override PoolVirtues Virtues => PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
    public override int Preference() => 1;
  }

  public override IEnumerable<INode> Children => Lhss.Concat<INode>(new[] { Expr });

  /// <summary>
  /// "assumeToken" is allowed to be "null", in which case the verifier will check that a RHS value exists.
  /// If "assumeToken" is non-null, then it should denote the "assume" keyword used in the statement.
  /// </summary>
  public AssignSuchThatStmt(IToken tok, IToken endTok, List<Expression> lhss, Expression expr, AttributedToken assumeToken, Attributes attrs)
    : base(tok, endTok, lhss, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(cce.NonNullElements(lhss));
    Contract.Requires(lhss.Count != 0);
    Contract.Requires(expr != null);
    Expr = expr;
    if (assumeToken != null) {
      AssumeToken = assumeToken;
    }
  }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      yield return Expr;
    }
  }
}