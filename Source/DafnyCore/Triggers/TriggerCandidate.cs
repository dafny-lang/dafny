using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny.Triggers;

/// <summary>
/// A trigger consist of a number of terms
/// </summary>
class TriggerCandidate {
  internal List<TriggerTerm> Terms { get; set; }
  internal string Annotation { get; set; }

  internal TriggerCandidate(List<TriggerTerm> terms) {
    this.Terms = terms;
  }

  public TriggerCandidate(TriggerCandidate candidate) {
    this.Terms = candidate.Terms;
  }

  internal bool MentionsAll(List<BoundVar> vars) {
    return vars.All(x => Terms.Any(term => term.Variables.Contains(x)));
  }

  private string Repr => String.Join(", ", Terms);

  public override string ToString() {
    return "{" + Repr + "}" + (String.IsNullOrWhiteSpace(Annotation) ? "" : " (" + Annotation + ")");
  }

  /// <summary>
  /// See section 2.2 of "Trigger Selection Strategies to Stabilize Program Verifiers" to learn
  /// how we find potentially looping subterms.
  /// 
  /// Roughly, this heuristic flags a trigger as potentially looping if
  /// instantiating the quantifier may lead to a ground term that again matches the trigger
  /// </summary>
  internal IEnumerable<TriggerMatch> LoopingSubterms(ComprehensionExpr quantifier, DafnyOptions options) {
    Contract.Requires(!(quantifier is QuantifierExpr) || ((QuantifierExpr)quantifier).SplitQuantifier == null); // Don't call this on a quantifier with a Split clause: it's not a real quantifier
    var matchingSubterms = MatchingSubterms(quantifier);
    var boundVars = new HashSet<BoundVar>(quantifier.BoundVars);
    return matchingSubterms.Where(tm => tm.CouldCauseLoops(Terms, boundVars, options));
  }

  private List<TriggerMatch> MatchingSubterms(ComprehensionExpr quantifier) {
    Contract.Requires(!(quantifier is QuantifierExpr) || ((QuantifierExpr)quantifier).SplitQuantifier == null); // Don't call this on a quantifier with a Split clause: it's not a real quantifier
    return Terms.SelectMany(term => quantifier.SubexpressionsMatchingTrigger(term.Expr)).Deduplicate(TriggerMatch.Eq);
  }

  internal bool IsStrongerThan(TriggerCandidate that) {
    if (this == that) {
      return false;
    }

    var hasStrictlyStrongerTerm = false;
    foreach (var t in Terms) {
      var comparison = that.Terms.Select(t.CompareTo).Max();

      // All terms of `this` must be at least as strong as a term of `that`
      if (comparison == TriggerTerm.TermComparison.NotStronger) { return false; }

      // Did we find a strictly stronger term?
      hasStrictlyStrongerTerm = hasStrictlyStrongerTerm || comparison == TriggerTerm.TermComparison.Stronger;
    }

    return hasStrictlyStrongerTerm;
  }
}