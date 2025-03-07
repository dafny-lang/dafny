// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#define DEBUG_AUTO_TRIGGERS

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny.Triggers {
  internal static class TriggerUtils {
    public static Attributes CopyAttributes(Attributes source) {
      return source == null ? null : new Attributes(source.Name, source.Args, CopyAttributes(source.Prev));
    }

    internal static List<T> MergeAlterFirst<T>(List<T> a, List<T> b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      a.AddRange(b);
      return a;
    }

    internal static ISet<T> MergeAlterFirst<T>(ISet<T> a, ISet<T> b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      a.UnionWith(b);
      return a;
    }

    internal static bool SameNullity<T>(T x1, T x2) where T : class {
      return (x1 == null) == (x2 == null);
    }

    internal static IEnumerable<Expression> MaybeWrapInOld(Expression expr, HashSet<OldExpr>/*?*/ wrap) {
      Contract.Requires(expr != null);
      Contract.Requires(wrap == null || wrap.Count != 0);
      if (wrap != null && !(expr is NameSegment) && !(expr is IdentifierExpr)) {
        foreach (var w in wrap) {
          var newExpr = new OldExpr(new AutoGeneratedOrigin(expr.Origin), expr, w.At) { AtLabel = w.AtLabel };
          newExpr.Type = expr.Type;
          yield return newExpr;
        }
      } else {
        yield return expr;
      }
    }
  }
}
