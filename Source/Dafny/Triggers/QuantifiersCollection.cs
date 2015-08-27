#define QUANTIFIER_WARNINGS

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Triggers {
  class QuantifierWithTriggers {
    internal QuantifierExpr quantifier;
    internal List<TriggerTerm> CandidateTerms;
    internal List<TriggerCandidate> Candidates;
    internal List<TriggerCandidate> RejectedCandidates;

    internal bool AllowsLoops { get { return TriggerUtils.AllowsMatchingLoops(quantifier); } }
    internal bool CouldSuppressLoops { get; set; }

    internal QuantifierWithTriggers(QuantifierExpr quantifier) {
      this.quantifier = quantifier;
      this.RejectedCandidates = new List<TriggerCandidate>();
    }

    internal void TrimInvalidTriggers() {
      Contract.Requires(CandidateTerms != null);
      Contract.Requires(Candidates != null);
      Candidates = TriggerUtils.Filter(Candidates, tr => tr, (tr, _) => tr.MentionsAll(quantifier.BoundVars), (tr, _) => { }).ToList();
    }
  }

  class QuantifiersCollection {
    readonly ErrorReporter reporter;
    readonly List<QuantifierWithTriggers> quantifiers;
   
    internal QuantifiersCollection(IEnumerable<QuantifierExpr> quantifiers, ErrorReporter reporter) {
      Contract.Requires(quantifiers.All(q => q.SplitQuantifier == null));
      this.reporter = reporter;
      this.quantifiers = quantifiers.Select(q => new QuantifierWithTriggers(q)).ToList();
    }

    internal void ComputeTriggers(TriggersCollector triggersCollector) {
      CollectAndShareTriggers(triggersCollector);
      TrimInvalidTriggers();
      BuildDependenciesGraph();
      SuppressMatchingLoops();
      SelectTriggers();
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
      var pool = quantifiers.SelectMany(q => triggersCollector.CollectTriggers(q.quantifier));
      var distinctPool = pool.Deduplicate(TriggerTerm.Eq);

      foreach (var q in quantifiers) {
        q.CandidateTerms = distinctPool; // The list of candidate terms is immutable
        q.Candidates = TriggerUtils.AllNonEmptySubsets(distinctPool, SubsetGenerationPredicate, q.quantifier.BoundVars).Select(set => set.ToTriggerCandidate()).ToList();
      }
    }

    private void TrimInvalidTriggers() {
      foreach (var q in quantifiers) {
        q.TrimInvalidTriggers();
      }
    }

    void BuildDependenciesGraph() {
      // The problem of finding matching loops between multiple-triggers is hard; it
      // seems to require one to track exponentially-sized dependencies between parts
      // of triggers and quantifiers. For now, we only do single-quantifier loop
      // detection
    }

    void SuppressMatchingLoops() {
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
      // The last thing that we ignore is matching variables against constants, 
      // to ensure that P(x) is not flagged as looping with P(0).
      // This ignoring logic is implemented by the CouldCauseLoops method.

      foreach (var q in quantifiers) {
        var looping = new List<TriggerCandidate>();

        var safe = TriggerUtils.Filter(
          q.Candidates,
          candidate => candidate.LoopingSubterms(q.quantifier).ToList(),
          (candidate, loopingSubterms) => !loopingSubterms.Any(),
          (candidate, loopingSubterms) => {
            looping.Add(candidate);
            candidate.Annotation = "may loop with " + loopingSubterms.MapConcat(t => "{" + Printer.ExprToString(t.OriginalExpr) + "}", ", ");
          }).ToList();

        q.CouldSuppressLoops = safe.Count > 0;

        if (!q.AllowsLoops && q.CouldSuppressLoops) {
          q.Candidates = safe;
          q.RejectedCandidates.AddRange(looping);
        }
      }
    }

    void SelectTriggers() {
      foreach (var q in quantifiers) { //FIXME Check whether this makes verification faster
        q.Candidates = TriggerUtils.Filter(q.Candidates,
          candidate => q.Candidates.Where(candidate.IsStrongerThan).ToList(),
          (candidate, weakerCandidates) => !weakerCandidates.Any(),
          (candidate, weakerCandidates) => {
            q.RejectedCandidates.Add(candidate);
            candidate.Annotation = "more specific than " + String.Join(", ", weakerCandidates);
          }).ToList();
      }
    }

    private void CommitOne(QuantifierWithTriggers q, bool addHeader) {
      var errorLevel = ErrorLevel.Info;
      var msg = new StringBuilder();
      var indent = addHeader ? "  " : "";

      if (!TriggerUtils.NeedsAutoTriggers(q.quantifier)) { // NOTE: matchingloop, split and autotriggers attributes are passed down to Boogie
        msg.AppendFormat("Not generating triggers for {{{0}}}.", Printer.ExprToString(q.quantifier.Term)).AppendLine(); 
      } else {
        if (addHeader) {
          msg.AppendFormat("For expression {{{0}}}:", Printer.ExprToString(q.quantifier.Term)).AppendLine();
        }

        foreach (var candidate in q.Candidates) {
          q.quantifier.Attributes = new Attributes("trigger", candidate.Terms.Select(t => t.Expr).ToList(), q.quantifier.Attributes);
        }

        AddTriggersToMessage("Selected triggers:", q.Candidates, msg, indent);
        AddTriggersToMessage("Rejected triggers:", q.RejectedCandidates, msg, indent, true);

#if QUANTIFIER_WARNINGS
        string WARN = indent + (DafnyOptions.O.UnicodeOutput ? "⚠ " : "(!) ");
        if (!q.CandidateTerms.Any()) {
          errorLevel = ErrorLevel.Warning;
          msg.Append(WARN).AppendLine("No terms found to trigger on.");
        } else if (!q.Candidates.Any()) {
          errorLevel = ErrorLevel.Warning;
          msg.Append(WARN).AppendLine("No trigger covering all quantified variables found.");
        } else if (!q.CouldSuppressLoops && !q.AllowsLoops) {
          errorLevel = ErrorLevel.Warning;
          msg.Append(WARN).AppendLine("Suppressing loops would leave this expression without triggers.");
        }
#endif
      }
      
      if (msg.Length > 0) {
        var msgStr = msg.ToString().TrimEnd("\r\n ".ToCharArray());
        reporter.Message(MessageSource.Rewriter, errorLevel, q.quantifier.tok, msgStr);
      }
    }

    private static void AddTriggersToMessage<T>(string header, List<T> triggers, StringBuilder msg, string indent, bool newlines = false) {
      if (triggers.Any()) {
        msg.Append(indent).Append(header);
        if (triggers.Count == 1) {
          msg.Append(" ");
        } else if (triggers.Count > 1) {
          msg.AppendLine().Append(indent).Append("  ");
        }
        var separator = newlines && triggers.Count > 1 ? Environment.NewLine + indent + "  " : ", ";
        msg.AppendLine(String.Join(separator, triggers));
      }
    }

    internal void CommitTriggers() {
      foreach (var q in quantifiers) {
        CommitOne(q, quantifiers.Count > 1);
      }
    }
  }
}
