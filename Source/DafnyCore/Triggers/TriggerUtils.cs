// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#define DEBUG_AUTO_TRIGGERS

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny.Triggers {
  class TriggerUtils {
    internal static List<T> CopyAndAdd<T>(List<T> seq, T elem) {
      var copy = new List<T>(seq);
      copy.Add(elem);
      return copy;
    }

    public static Attributes CopyAttributes(Attributes source) {
      if (source == null) {
        return null;
      } else {
        return new Attributes(source.Name, source.Args, CopyAttributes(source.Prev));
      }
    }

    internal class SetOfTerms {
      internal bool IsRedundant { get; private set; }
      internal List<TriggerTerm> Terms { get; set; }

      private ISet<BoundVar> variables;
      private Dictionary<BoundVar, TriggerTerm> termOwningAUniqueVar;
      private Dictionary<TriggerTerm, ISet<BoundVar>> uniqueVarsOwnedByATerm;

      public int Count { get { return Terms.Count; } }

      private SetOfTerms() { }

      internal TriggerCandidate ToTriggerCandidate() {
        return new TriggerCandidate(Terms);
      }

      internal static SetOfTerms Empty() {
        var newSet = new SetOfTerms();
        newSet.IsRedundant = false;
        newSet.Terms = new List<TriggerTerm>();
        newSet.variables = new HashSet<BoundVar>();
        newSet.termOwningAUniqueVar = new Dictionary<BoundVar, TriggerTerm>();
        newSet.uniqueVarsOwnedByATerm = new Dictionary<TriggerTerm, ISet<BoundVar>>();
        return newSet;
      }

      /// <summary>
      /// Simple formulas like [P0(i) && P1(i) && P2(i) && P3(i) && P4(i)] yield very
      /// large numbers of multi-triggers, most of which are useless. As it copies its
      /// argument, this method updates various datastructures that allow it to
      /// efficiently track ownership relations between formulae and bound variables,
      /// and sets the IsRedundant flag of the returned set, allowing the caller to
      /// discard that set of terms, and the ones that would have been built on top of
      /// it, thus ensuring that the only sets of terms produced in the end are sets
      /// of terms in which each element contributes (owns) at least one variable.
      ///
      /// Note that this is trickier than just checking every term for new variables;
      /// indeed, a new term that does bring new variables in can make an existing
      /// term redundant (see redundancy-detection-does-its-job-properly.dfy).
      /// </summary>
      internal SetOfTerms CopyWithAdd(TriggerTerm term, ISet<BoundVar> relevantVariables) {
        var copy = new SetOfTerms();
        copy.Terms = new List<TriggerTerm>(Terms);
        copy.variables = new HashSet<BoundVar>(variables);
        copy.termOwningAUniqueVar = new Dictionary<BoundVar, TriggerTerm>(termOwningAUniqueVar);
        copy.uniqueVarsOwnedByATerm = new Dictionary<TriggerTerm, ISet<BoundVar>>(uniqueVarsOwnedByATerm);

        copy.Terms.Add(term);

        var varsInNewTerm = new HashSet<BoundVar>(term.BoundVars);
        varsInNewTerm.IntersectWith(relevantVariables);

        var ownedByNewTerm = new HashSet<BoundVar>();

        // Check #0: does this term bring anything new?
        copy.IsRedundant = IsRedundant || varsInNewTerm.All(bv => copy.variables.Contains(bv));
        copy.variables.UnionWith(varsInNewTerm);

        // Check #1: does this term claiming ownership of all its variables cause another term to become useless?
        foreach (var v in varsInNewTerm) {
          TriggerTerm originalOwner;
          if (copy.termOwningAUniqueVar.TryGetValue(v, out originalOwner)) {
            var alsoOwnedByOriginalOwner = copy.uniqueVarsOwnedByATerm[originalOwner];
            alsoOwnedByOriginalOwner.Remove(v);
            if (!alsoOwnedByOriginalOwner.Any()) {
              copy.IsRedundant = true;
            }
          } else {
            ownedByNewTerm.Add(v);
            copy.termOwningAUniqueVar[v] = term;
          }
        }

        // Actually claim ownership
        copy.uniqueVarsOwnedByATerm[term] = ownedByNewTerm;

        return copy;
      }
    }

    internal static IEnumerable<SetOfTerms> AllSubsets(IList<TriggerTerm> source, Func<SetOfTerms, TriggerTerm, bool> predicate, int offset, ISet<BoundVar> relevantVariables) {
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

    internal static bool SameLists<T>(IEnumerable<T> list1, IEnumerable<T> list2, Func<T, T, bool> comparer) {
      if (ReferenceEquals(list1, list2)) {
        return true;
      } else if ((list1 == null) != (list2 == null)) {
        return false;
      }

      var it1 = list1.GetEnumerator();
      var it2 = list2.GetEnumerator();
      bool it1_has, it2_has;
      bool acc = true;

      do {
        it1_has = it1.MoveNext();
        it2_has = it2.MoveNext();

        if (it1_has == true && it2_has == true) {
          acc = acc && comparer(it1.Current, it2.Current);
        }
      } while (it1_has && it2_has);

      return it1_has == it2_has && acc;
    }

    internal static IEnumerable<T> Filter<T, U>(IEnumerable<T> elements, Func<T, U> Converter, Func<T, U, bool> predicate, Action<T, U> reject) {
      var positive = new List<T>();
      foreach (var elem in elements) {
        var conv = Converter(elem);
        if (predicate(elem, conv)) {
          yield return elem;
        } else {
          reject(elem, conv);
        }
      }
    }

    internal static bool SameNullity<T>(T x1, T x2) where T : class {
      return (x1 == null) == (x2 == null);
    }

    internal string JoinStringsWithHeader(string header, IEnumerable<string> lines) {
      return header + String.Join(Environment.NewLine + new String(' ', header.Length), lines);
    }

    [Conditional("DEBUG_AUTO_TRIGGERS")]
    internal static void DebugTriggers(string format, params object[] more) {
      Console.Error.WriteLine(format, more);
    }

    internal static bool AllowsMatchingLoops(ComprehensionExpr quantifier) {
      Contract.Requires(!(quantifier is QuantifierExpr) || ((QuantifierExpr)quantifier).SplitQuantifier == null); // Don't call this on a quantifier with a Split clause: it's not a real quantifier
      // This is different from nowarn: it won't remove loops at all, even if another trigger is available.
      return Attributes.Contains(quantifier.Attributes, "matchingloop");
    }

    internal static bool WantsAutoTriggers(ComprehensionExpr quantifier) {
      Contract.Requires(!(quantifier is QuantifierExpr) || ((QuantifierExpr)quantifier).SplitQuantifier == null); // Don't call this on a quantifier with a Split clause: it's not a real quantifier
      bool wantsAutoTriggers = true;
      return !Attributes.ContainsBool(quantifier.Attributes, "autotriggers", ref wantsAutoTriggers) || wantsAutoTriggers;
    }

    internal static bool NeedsAutoTriggers(ComprehensionExpr quantifier) {
      Contract.Requires(!(quantifier is QuantifierExpr) || ((QuantifierExpr)quantifier).SplitQuantifier == null); // Don't call this on a quantifier with a Split clause: it's not a real quantifier
      return !Attributes.Contains(quantifier.Attributes, "trigger") && WantsAutoTriggers(quantifier);
    }

    internal static bool WantsMatchingLoopRewrite(ComprehensionExpr quantifier) {
      Contract.Requires(!(quantifier is QuantifierExpr) || ((QuantifierExpr)quantifier).SplitQuantifier == null);
      bool wantsMatchingLoopRewrite = true;
      return (!Attributes.ContainsBool(quantifier.Attributes, "matchinglooprewrite", ref wantsMatchingLoopRewrite) || wantsMatchingLoopRewrite) && WantsAutoTriggers(quantifier);
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
            expr = new BinaryExpr(bin.RangeToken, BinaryExpr.Opcode.In, bin.E0, bin.E1) {
              ResolvedOp = RemoveNotInBinaryExprIn(bin.ResolvedOp),
              Type = bin.Type
            };
          } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.InMultiSet) {
            expr = new SeqSelectExpr(bin.RangeToken, true, bin.E1, bin.E0, null) {
              Type = bin.Type
            };
            isKiller = true; // [a in s] becomes [s[a] > 0], which is a trigger killer
          } else {
            var newOpcode = ChangeProperToInclusiveContainment(bin.ResolvedOp);
            if (newOpcode != bin.ResolvedOp) {
              // For sets, isets, and multisets, change < to <= in triggers (and analogously
              // > to >=), since "a < b" translates as "a <= b && !(b <= a)" or
              // "a <= b && !(a == b)".
              expr = new BinaryExpr(bin.RangeToken, BinaryExpr.ResolvedOp2SyntacticOp(newOpcode), bin.E0, bin.E1) {
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
      bool _;
      return PrepareExprForInclusionInTrigger(expr, out _);
    }

    internal static IEnumerable<Expression> MaybeWrapInOld(Expression expr, HashSet<OldExpr>/*?*/ wrap) {
      Contract.Requires(expr != null);
      Contract.Requires(wrap == null || wrap.Count != 0);
      if (wrap != null && !(expr is NameSegment) && !(expr is IdentifierExpr)) {
        foreach (var w in wrap) {
          var newExpr = new OldExpr(expr.RangeToken.MakeAutoGenerated(), expr, w.At) { AtLabel = w.AtLabel };
          newExpr.Type = expr.Type;
          yield return newExpr;
        }
      } else {
        yield return expr;
      }
    }
  }
}
