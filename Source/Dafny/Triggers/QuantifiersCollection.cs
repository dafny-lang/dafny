using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

//FIXME Generated triggers should be _triggers
//FIXME: When scoring, do not consider old(x) to be higher than x.

namespace Microsoft.Dafny.Triggers {
  class QuantifierWithTriggers {
    internal QuantifierExpr quantifier;
    internal List<MultiTriggerCandidate> triggers;

    internal QuantifierWithTriggers(QuantifierExpr quantifier) {
      this.quantifier = quantifier;
      this.triggers = null;
    }

    internal void TrimInvalidTriggers() {
      triggers = triggers.Where(tr => tr.MentionsAll(quantifier.BoundVars)).ToList();
    }

    public bool QuantifierAlreadyHadTriggers { get { return !TriggerUtils.NeedsAutoTriggers(quantifier); } }
  }

  class QuantifiersCollection {
    readonly ErrorReporter reporter;
    readonly List<QuantifierWithTriggers> quantifiers;
   
    internal QuantifiersCollection(IEnumerable<QuantifierExpr> quantifiers, ErrorReporter reporter) {
      this.reporter = reporter;
      this.quantifiers = quantifiers.Select(q => new QuantifierWithTriggers(q)).ToList();
    }

    void ComputeTriggers() {
      CollectAndShareTriggers();
      TrimInvalidTriggers();
      BuildDependenciesGraph();
      SuppressMatchingLoops();
      SelectTriggers();
    }

    void CollectAndShareTriggers() {
      var pool = quantifiers.SelectMany(q => TriggersCollector.CollectTriggers(q.quantifier));
      var distinctPool = pool.Deduplicate((x, y) => ExprExtensions.ExpressionEq(x.Expr, y.Expr));
      var multiPool = TriggerUtils.AllNonEmptySubsets(distinctPool).Select(candidates => new MultiTriggerCandidate(candidates)).ToList();

      foreach (var q in quantifiers) {
        if (q.QuantifierAlreadyHadTriggers) {
          reporter.Info(MessageSource.Resolver, q.quantifier.tok, "Not generating triggers for this quantifier."); //FIXME: no_trigger is passed down to Boogie
          return;
        } else {
          q.triggers = multiPool;
        }
      }
    }

    private void TrimInvalidTriggers() {
      foreach (var q in quantifiers) {
        q.TrimInvalidTriggers();
      }
    }

    void BuildDependenciesGraph() {
      //FIXME
    }

    void SuppressMatchingLoops() {
      //FIXME
    }

    void SelectTriggers() {
      //FIXME
    }

    private void CommitOne(QuantifierWithTriggers q) {
      foreach (var multiCandidate in q.triggers) { //TODO: error message for when no triggers found
        q.quantifier.Attributes = new Attributes("trigger", multiCandidate.terms.Select(t => t.Expr).ToList(), q.quantifier.Attributes);
      }


      //TriggerUtils.DebugTriggers("  Final results:\n{0}", PickMultiTriggers(quantifier));

      //var multi_candidates = PickMultiTriggers(quantifier);

      //if (multi_candidates.RejectedMultiCandidates.Any()) {
      //  var tooltip = TriggerUtils.JoinStringsWithHeader("Rejected: ", multi_candidates.RejectedMultiCandidates.Where(candidate => candidate.Tags != null)
      //    .Select(candidate => candidate.AsDafnyAttributeString(true, true)));
      //  reporter.Info(ErrorSource.Resolver, quantifier.tok, tooltip, quantifier.tok.val.Length);
      //}

      //if (multi_candidates.FinalMultiCandidates.Any()) {
      //  var tooltip = JoinStringsWithHeader("Triggers: ", multi_candidates.FinalMultiCandidates.Select(multi_candidate => multi_candidate.AsDafnyAttributeString()));
      //  reporter.Info(ErrorSource.Resolver, quantifier.tok, tooltip, quantifier.tok.val.Length);
      //}

      //string warning = multi_candidates.Warning();
      //if (warning != null) {
      //  // FIXME reenable Resolver.Warning(quantifier.tok, warning);
      //}
    }

  }
}
