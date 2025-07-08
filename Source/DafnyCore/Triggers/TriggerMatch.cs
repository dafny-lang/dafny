using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.Triggers;

internal struct TriggerMatch {
  internal Expression Expr;
  internal Expression OriginalExpr;
  internal Dictionary<IVariable, Expression> Bindings;

  internal static bool Eq(TriggerMatch t1, TriggerMatch t2) {
    return ExprExtensions.ExpressionEq(t1.Expr, t2.Expr);
  }

  /// <summary>
  ///  This method checks whether this match could actually cause a loop, given a set of terms participating in a trigger;
  ///  to compute an answer, we match the Expr of this match against the Exprs of each of these term, allowing for harmless
  ///  variations. If any of these tests does match, this term likely won't cause a loop.
  ///  The boundVars list is useful to determine that forall x :: P(x) == P(y+z) does not loop.
  /// </summary>
  internal bool CouldCauseLoops(List<TriggerTerm> terms, ISet<BoundVar> boundVars, DafnyOptions options) {
    var expr = Expr;
    return !terms.Any(term => term.Expr.ExpressionEqModuloExpressionsNotInvolvingBoundVariables(expr, boundVars, options));
  }
}