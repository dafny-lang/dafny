// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Triggers {
  
  // TODO rename. ComprehensionSplitsTriggerWriter ??? UnsplitsComprehensionTriggerWriter?
  class ComprehensionContainerTriggerWriter {
    private readonly ErrorReporter reporter;
    private readonly ComprehensionExpr comprehensionContainer;  //  the expression where the splits are originated from
    private List<TriggerWriter> triggerWriters;

    internal ComprehensionContainerTriggerWriter(ComprehensionExpr comprehensionContainer, IEnumerable<ComprehensionExpr> quantifiers, ErrorReporter reporter) {
      Contract.Requires(quantifiers.All(q => !(q is QuantifierExpr) || ((QuantifierExpr)q).SplitQuantifier == null));
      this.reporter = reporter;
      this.comprehensionContainer = comprehensionContainer;
      triggerWriters = quantifiers.Select(q => new TriggerWriter(q)).ToList();
    }

    internal void ComputeTriggers(TriggersCollector triggersCollector) {
      CollectAndShareTriggers(triggersCollector);
      TrimInvalidTriggers();
      BuildDependenciesGraph();
      if (DetectAndFilterLoopingCandidates() && RewriteMatchingLoop(triggersCollector.ForModule)) {
        CollectWithoutShareTriggers(triggersCollector);
        TrimInvalidTriggers();
        DetectAndFilterLoopingCandidates();
      }
      FilterWeakerTriggers();
      CombineSplitQuantifier();
    }

    private bool SubsetGenerationPredicate(TriggerUtils.SetOfTerms terms, TriggerTerm additionalTerm) {
      return true; // FIXME Remove this
      //return additionalTerm.Variables.Where(v => v is BoundVar && !terms.Any(t => t.Variables.Contains(v))).Any();
    }

    /// <summary>
    /// Collect triggers from the body of each quantifier, and share them
    /// between all quantifiers. This method assumes that all quantifiers
    /// actually come from the same context, and were the result of a split that
    /// gave them all the same variables.
    /// </summary>
    /// <param name="triggersCollector"></param>
    void CollectAndShareTriggers(TriggersCollector triggersCollector) {
      var pool = new List<TriggerTerm>();
      foreach (var triggerWriter in triggerWriters) {
        var candidates = triggersCollector.CollectTriggers(triggerWriter.Comprehension).Deduplicate(TriggerTerm.Eq);
        var greatTerms = candidates.Where(term => !triggersCollector.TranslateToFunctionCall(term.Expr)).ToList();
        if (greatTerms.Any()) {
          // If we have great terms, only use those
          candidates = greatTerms;
        }
        pool.AddRange(candidates);
      }
      var distinctPool = pool.Deduplicate(TriggerTerm.Eq);

      foreach (var triggerWriter in triggerWriters) {
        triggerWriter.CandidateTerms = distinctPool; // The list of candidate terms is immutable
        triggerWriter.Candidates = TriggerUtils.AllNonEmptySubsets(distinctPool, SubsetGenerationPredicate, triggerWriter.Comprehension.BoundVars)
          .Select(set => set.ToTriggerCandidate()).ToList();
      }
    }

    void CollectWithoutShareTriggers(TriggersCollector triggersCollector) {
      foreach (var triggerWriter in triggerWriters) {
        var candidates = triggersCollector.CollectTriggers(triggerWriter.Comprehension).Deduplicate(TriggerTerm.Eq);
        triggerWriter.CandidateTerms = candidates; // The list of candidate terms is immutable
        triggerWriter.Candidates = TriggerUtils.AllNonEmptySubsets(candidates, SubsetGenerationPredicate, triggerWriter.Comprehension.BoundVars).Select(set => set.ToTriggerCandidate()).ToList();
      }
    }

    private void TrimInvalidTriggers() {
      foreach (var triggerWriter in triggerWriters) {
        triggerWriter.TrimInvalidTriggers();
      }
    }

    void BuildDependenciesGraph() {
      // The problem of finding matching loops between multiple-triggers is hard; it
      // seems to require one to track exponentially-sized dependencies between parts
      // of triggers and quantifiers. For now, we only do single-quantifier loop
      // detection
    }

    bool DetectAndFilterLoopingCandidates() {
      // NOTE: This only looks for self-loops; that is, loops involving a single
      // quantifier.

      // For a given quantifier q, we introduce a triggering relation between trigger
      // candidates by writing t1 → t2 if instantiating q from t1 introduces a ground
      // term that matches t2. Then, we notice that this relation is transitive, since
      // all triggers yield the same set of terms. This means that any matching loop
      // t1 → ... → t1 can be reduced to a self-loop t1 → t1. Detecting such
      // self-loops is then only a matter of finding terms in the body of the
      // quantifier that match a given trigger.

      // Of course, each trigger that actually appears in the body of the quantifier
      // yields a trivial self-loop (e.g. P(i) in [∀ i {P(i)} ⋅ P(i)]), so we
      // ignore this type of loops. In fact, we ignore any term in the body of the
      // quantifier that matches one of the terms of the trigger (this ensures that
      // [∀ x {f(x), f(f(x))} ⋅ f(x) = f(f(x))] is not a loop). And we even
      // ignore terms that almost match a trigger term, modulo a single variable
      // (this ensures that [∀ x y {a(x, y)} ⋅ a(x, y) == a(y, x)] is not a loop).
      
      // In addition, we ignore cases where the only differences between a trigger
      // and a trigger match are places where a variable is replaced with an
      // expression whose free variables do not intersect that of the quantifier
      // in which that expression is found. For examples of this behavious, see
      // triggers/literals-do-not-cause-loops.
      // This ignoring logic is implemented by the CouldCauseLoops method.
      bool foundLoop = false;
      foreach (var quantifier in triggerWriters) {
        foundLoop |= quantifier.DetectAndFilterLoopingCandidates(reporter);
      }
      return foundLoop;
    }

    private bool RewriteMatchingLoop(ModuleDefinition module) {
      if (comprehensionContainer is QuantifierExpr unSplitQuantifier) {
        bool rewritten = false;
        foreach (var triggerWriter in triggerWriters) {
          rewritten |= triggerWriter.RewriteMatchingLoop(reporter, module);
        }
        if (rewritten) {
          unSplitQuantifier.SplitQuantifier = triggerWriters.Select(q => (Expression)q.Comprehension).ToList();
          return true;
        }
      }
      return false;
    }

    void FilterWeakerTriggers() {
      foreach (var triggerWriter in triggerWriters) {
        triggerWriter.FilterStrongCandidates();
      }
    }

    private class QuantifierGroup {
      internal TriggerWriter quantifier;
      internal List<ComprehensionExpr> expressions;

      public QuantifierGroup(TriggerWriter q, List<ComprehensionExpr> expressions) {
        this.quantifier = q;
        this.expressions = expressions;
      }
    }

    // group split quantifier by what triggers they got, and merged them back into one quantifier.
    private void CombineSplitQuantifier() {
      if (triggerWriters.Count > 1) {
        var groups = new List<QuantifierGroup>();
        groups.Add(new QuantifierGroup(triggerWriters[0], new List<ComprehensionExpr> { triggerWriters[0].Comprehension }));
        for (int i = 1; i < triggerWriters.Count; i++) {
          bool found = false;
          for (int j = 0; j < groups.Count; j++) {
            if (HasSameTriggers(triggerWriters[i], groups[j].quantifier)) {
              // belong to the same group
              groups[j].expressions.Add(triggerWriters[i].Comprehension);
              found = true;
              break;
            }
          }
          if (!found) {
            // start a new group
            groups.Add(new QuantifierGroup(triggerWriters[i], new List<ComprehensionExpr> { triggerWriters[i].Comprehension }));
          }
        }
        if (groups.Count == triggerWriters.Count) {
          // have the same number of splits, so no splits are combined.
          return;
        }
        // merge expressions in each group back to one quantifier.
        List<TriggerWriter> list = new List<TriggerWriter>();
        List<Expression> splits = new List<Expression>();
        foreach (var group in groups) {
          TriggerWriter q = group.quantifier;
          if (q.Comprehension is ForallExpr forallExpr) {
            IToken tok = forallExpr.tok is NestedToken nestedToken ? nestedToken.Outer : forallExpr.tok;
            Expression expr = QuantifiersToExpression(tok, BinaryExpr.ResolvedOpcode.And, group.expressions);
            q.Comprehension = new ForallExpr(tok, forallExpr.RangeToken, forallExpr.BoundVars, forallExpr.Range, expr, TriggerUtils.CopyAttributes(forallExpr.Attributes)) { Type = forallExpr.Type, Bounds = forallExpr.Bounds };
          } else if (q.Comprehension is ExistsExpr existsExpr) {
            IToken tok = existsExpr.tok is NestedToken nestedToken ? nestedToken.Outer : existsExpr.tok;
            Expression expr = QuantifiersToExpression(tok, BinaryExpr.ResolvedOpcode.Or, group.expressions);
            q.Comprehension = new ExistsExpr(tok, existsExpr.RangeToken, existsExpr.BoundVars, existsExpr.Range, expr, TriggerUtils.CopyAttributes(existsExpr.Attributes)) { Type = existsExpr.Type, Bounds = existsExpr.Bounds };
          }
          list.Add(q);
          splits.Add(q.Comprehension);
        }

        triggerWriters = list;
        Contract.Assert(this.comprehensionContainer is QuantifierExpr); // only QuantifierExpr has SplitQuantifier
        ((QuantifierExpr)this.comprehensionContainer).SplitQuantifier = splits;
      }
    }

    private bool HasSameTriggers(TriggerWriter one, TriggerWriter other) {
      return TriggerUtils.SameLists(one.Candidates, other.Candidates, SameTriggerCandidate);
    }

    private static bool SameTriggerCandidate(TriggerCandidate arg1, TriggerCandidate arg2) {
      return TriggerUtils.SameLists(arg1.Terms, arg2.Terms, TriggerTerm.Eq);
    }

    private Expression QuantifiersToExpression(IToken tok, BinaryExpr.ResolvedOpcode op, List<ComprehensionExpr> expressions) {
      var expr = expressions[0].Term;
      for (int i = 1; i < expressions.Count; i++) {
        expr = new BinaryExpr(tok, op, expr, expressions[i].Term);
      }
      return expr;
    }

    internal void CommitTriggers(SystemModuleManager systemModuleManager) {
      foreach (var triggerWriter in triggerWriters) {
        triggerWriter.CommitTrigger(reporter, systemModuleManager);
      }
    }
  }
}
