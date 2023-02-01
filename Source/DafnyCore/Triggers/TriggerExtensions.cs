// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#define THROW_UNSUPPORTED_COMPARISONS

using Microsoft.Dafny;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using Microsoft.Dafny.ExprExtensions;

namespace Microsoft.Dafny.Triggers {
  internal static class DeduplicateExtension {
    public static List<T> Deduplicate<T>(this IEnumerable<T> seq, Func<T, T, bool> eq) {
      List<T> deduplicated = new List<T>();

      foreach (var elem in seq) {
        if (!deduplicated.Any(other => eq(elem, other))) {
          deduplicated.Add(elem);
        }
      }

      return deduplicated;
    }
  }

  internal struct TriggerMatch {
    internal Expression Expr;
    internal Expression OriginalExpr;
    internal Dictionary<IVariable, Expression> Bindings;

    internal static bool Eq(TriggerMatch t1, TriggerMatch t2) {
      return t1.Expr.ExpressionEq(t2.Expr);
    }

    /// <summary>
    ///  This method checks whether this match could actually cause a loop, given a set of terms participating in a trigger;
    ///  to compute an answer, we match the Expr of this match against the Exprs of each of these term, allowing for harmless
    ///  variations. If any of these tests does match, this term likely won't cause a loop.
    ///  The boundVars list is useful to determine that forall x :: P(x) == P(y+z) does not loop.
    /// </summary>
    internal bool CouldCauseLoops(List<TriggerTerm> terms, ISet<BoundVar> boundVars) {
      var expr = Expr;
      return !terms.Any(term => term.Expr.ExpressionEqModuloExpressionsNotInvolvingBoundVariables(expr, boundVars));
    }
  }
}
