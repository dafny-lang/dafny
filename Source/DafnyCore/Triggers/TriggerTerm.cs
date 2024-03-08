using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.Triggers;

/// <summary>
/// A trigger may consist of several terms. A term must match with a ground term for the trigger to be active.
/// </summary>
internal class TriggerTerm {
  internal Expression Expr { get; init; }
  internal Expression OriginalExpr { get; set; }
  internal ISet<IVariable> Variables { get; init; }
  internal IEnumerable<BoundVar> BoundVars => Variables.Select(v => v as BoundVar).Where(v => v != null);

  public override string ToString() {
    return Printer.ExprToString(DafnyOptions.DefaultImmutableOptions, Expr);
    // NOTE: Using OriginalExpr here could cause some confusion:
    // for example, {a !in b} is a binary expression, yielding
    // trigger {a in b}. Saying the trigger is a !in b would be
    // rather misleading.
  }

  internal enum TermComparison {
    SameStrength = 0, Stronger = 1, NotStronger = -1
  }

  internal TermComparison CompareTo(TriggerTerm other) {
    if (this == other) {
      return TermComparison.SameStrength;
    } else if (Expr.AllSubExpressions(true, true).Any(other.Expr.ExpressionEq)) {
      return TermComparison.Stronger;
    } else {
      return TermComparison.NotStronger;
    }
  }

  internal static bool Eq(TriggerTerm t1, TriggerTerm t2) {
    return t1.Expr.ExpressionEq(t2.Expr);
  }
}