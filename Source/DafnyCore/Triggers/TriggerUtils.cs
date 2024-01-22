// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#define DEBUG_AUTO_TRIGGERS

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Triggers {
  internal static class TriggerUtils {
    public static Attributes CopyAttributes(Attributes source) {
      if (source == null) {
        return null;
      } else {
        return new Attributes(source.Name, source.Args, CopyAttributes(source.Prev));
      }
    }
    
    public static IEnumerable<SetOfTerms> AllSubsets(IList<TriggerTerm> source, Func<SetOfTerms, TriggerTerm, bool> predicate, int offset, ISet<BoundVar> relevantVariables) {
      if (offset >= source.Count) {
        yield return SetOfTerms.Empty();
        yield break;
      }

      foreach (var subset in AllSubsets(source, predicate, offset + 1, relevantVariables)) {
        var newSet = subset.CopyWithAdd(source[offset], relevantVariables);
        if (!newSet.IsRedundant && predicate(subset, source[offset])) { // Fixme remove the predicate?
          yield return newSet;
        }
        yield return subset;
      }
    }

    internal static IEnumerable<SetOfTerms> AllNonEmptySubsets(IList<TriggerTerm> source, Func<SetOfTerms, TriggerTerm, bool> predicate, IEnumerable<BoundVar> relevantVariables) {
      foreach (var subset in AllSubsets(source, predicate, 0, new HashSet<BoundVar>(relevantVariables))) {
        if (subset.Count > 0) {
          yield return subset;
        }
      }
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


    private static BinaryExpr.ResolvedOpcode RemoveNotInBinaryExprIn(BinaryExpr.ResolvedOpcode opcode) {
      switch (opcode) {
        case BinaryExpr.ResolvedOpcode.NotInMap:
          return BinaryExpr.ResolvedOpcode.InMap;
        case BinaryExpr.ResolvedOpcode.NotInSet:
          return BinaryExpr.ResolvedOpcode.InSet;
        case BinaryExpr.ResolvedOpcode.NotInSeq:
          return BinaryExpr.ResolvedOpcode.InSeq;
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
          return BinaryExpr.ResolvedOpcode.InMultiSet;
      }

      Contract.Assert(false);
      throw new ArgumentException();
    }

    private static BinaryExpr.ResolvedOpcode ChangeProperToInclusiveContainment(BinaryExpr.ResolvedOpcode opcode) {
      return opcode switch {
        BinaryExpr.ResolvedOpcode.ProperSubset => BinaryExpr.ResolvedOpcode.Subset,
        BinaryExpr.ResolvedOpcode.ProperMultiSubset => BinaryExpr.ResolvedOpcode.MultiSubset,
        BinaryExpr.ResolvedOpcode.ProperSuperset => BinaryExpr.ResolvedOpcode.Superset,
        BinaryExpr.ResolvedOpcode.ProperMultiSuperset => BinaryExpr.ResolvedOpcode.MultiSuperset,
        _ => opcode
      };
    }

    internal static Expression PrepareExprForInclusionInTrigger(Expression expr, out bool isKiller) {
      isKiller = false;

      Expression ret;
      do {
        ret = expr;
        if (expr is BinaryExpr bin) {
          if (bin.Op == BinaryExpr.Opcode.NotIn) {
            expr = new BinaryExpr(bin.tok, BinaryExpr.Opcode.In, bin.E0, bin.E1) {
              ResolvedOp = RemoveNotInBinaryExprIn(bin.ResolvedOp),
              Type = bin.Type
            };
          } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.InMultiSet) {
            expr = new SeqSelectExpr(bin.tok, true, bin.E1, bin.E0, null, null) {
              Type = bin.Type
            };
            isKiller = true; // [a in s] becomes [s[a] > 0], which is a trigger killer
          } else {
            var newOpcode = ChangeProperToInclusiveContainment(bin.ResolvedOp);
            if (newOpcode != bin.ResolvedOp) {
              // For sets, isets, and multisets, change < to <= in triggers (and analogously
              // > to >=), since "a < b" translates as "a <= b && !(b <= a)" or
              // "a <= b && !(a == b)".
              expr = new BinaryExpr(bin.tok, BinaryExpr.ResolvedOp2SyntacticOp(newOpcode), bin.E0, bin.E1) {
                ResolvedOp = newOpcode,
                Type = bin.Type
              };
            }
          }
        }
      } while (ret != expr);

      return ret;
    }

    internal static Expression PrepareExprForInclusionInTrigger(Expression expr) {
      return PrepareExprForInclusionInTrigger(expr, out var @_);
    }

    internal static IEnumerable<Expression> MaybeWrapInOld(Expression expr, HashSet<OldExpr>/*?*/ wrap) {
      Contract.Requires(expr != null);
      Contract.Requires(wrap == null || wrap.Count != 0);
      if (wrap != null && !(expr is NameSegment) && !(expr is IdentifierExpr)) {
        foreach (var w in wrap) {
          var newExpr = new OldExpr(new AutoGeneratedToken(expr.tok), expr, w.At) { AtLabel = w.AtLabel };
          newExpr.Type = expr.Type;
          yield return newExpr;
        }
      } else {
        yield return expr;
      }
    }
  }
}
