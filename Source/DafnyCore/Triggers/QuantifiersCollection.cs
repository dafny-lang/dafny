// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#define QUANTIFIER_WARNINGS

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;
using static Microsoft.Dafny.ErrorRegistry;

namespace Microsoft.Dafny.Triggers {
  class QuantifierWithTriggers {
    internal ComprehensionExpr quantifier;
    internal List<TriggerTerm> CandidateTerms;
    internal List<TriggerCandidate> Candidates;
    internal List<TriggerCandidate> RejectedCandidates;
    internal List<TriggerMatch> LoopingMatches;

    internal bool AllowsLoops { get { return TriggerUtils.AllowsMatchingLoops(quantifier); } }
    internal bool CouldSuppressLoops { get; set; }

    internal QuantifierWithTriggers(ComprehensionExpr quantifier) {
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
    readonly ComprehensionExpr expr;  //  the expression where the splits are originated from
    List<QuantifierWithTriggers> quantifiers;

    internal QuantifiersCollection(ComprehensionExpr expr, IEnumerable<ComprehensionExpr> quantifiers, ErrorReporter reporter) {
      Contract.Requires(quantifiers.All(q => !(q is QuantifierExpr) || ((QuantifierExpr)q).SplitQuantifier == null));
      this.reporter = reporter;
      this.expr = expr;
      this.quantifiers = quantifiers.Select(q => new QuantifierWithTriggers(q)).ToList();
    }

    internal void ComputeTriggers(TriggersCollector triggersCollector) {
      CollectAndShareTriggers(triggersCollector);
      TrimInvalidTriggers();
      BuildDependenciesGraph();
      if (SuppressMatchingLoops() && RewriteMatchingLoop()) {
        CollectWithoutShareTriggers(triggersCollector);
        TrimInvalidTriggers();
        SuppressMatchingLoops();
      }
      SelectTriggers();
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
      List<TriggerTerm> pool = new List<TriggerTerm>();
      foreach (var q in quantifiers) {
        var candidates = triggersCollector.CollectTriggers(q.quantifier).Deduplicate(TriggerTerm.Eq);
        // filter out the candidates that was "second-class"
        var filtered = TriggerUtils.Filter(candidates, tr => tr, (tr, _) => !tr.IsTranslatedToFunctionCall(), (tr, _) => { }).ToList();
        // if there are only "second-class" candidates, add them back.
        if (filtered.Count == 0) {
          filtered = candidates;
        }
        pool.AddRange(filtered);
      }
      var distinctPool = pool.Deduplicate(TriggerTerm.Eq);

      foreach (var q in quantifiers) {
        q.CandidateTerms = distinctPool; // The list of candidate terms is immutable
        q.Candidates = TriggerUtils.AllNonEmptySubsets(distinctPool, SubsetGenerationPredicate, q.quantifier.BoundVars)
          .Select(set => set.ToTriggerCandidate()).ToList();
      }
    }

    void CollectWithoutShareTriggers(TriggersCollector triggersCollector) {
      foreach (var q in quantifiers) {
        var candidates = triggersCollector.CollectTriggers(q.quantifier).Deduplicate(TriggerTerm.Eq);
        q.CandidateTerms = candidates; // The list of candidate terms is immutable
        q.Candidates = TriggerUtils.AllNonEmptySubsets(candidates, SubsetGenerationPredicate, q.quantifier.BoundVars).Select(set => set.ToTriggerCandidate()).ToList();
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

    bool SuppressMatchingLoops() {
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
      bool foundloop = false;
      foreach (var q in quantifiers) {
        var looping = new List<TriggerCandidate>();
        var loopingMatches = new List<TriggerMatch>();

        var safe = TriggerUtils.Filter(
          q.Candidates,
          candidate => candidate.LoopingSubterms(q.quantifier).ToList(),
          (candidate, loopingSubterms) => !loopingSubterms.Any(),
          (candidate, loopingSubterms) => {
            looping.Add(candidate);
            loopingMatches = loopingSubterms.ToList();
            candidate.Annotation = "may loop with " + loopingSubterms.MapConcat(t => "\"" + Printer.ExprToString(t.OriginalExpr) + "\"", ", ");
          }).ToList();

        q.CouldSuppressLoops = safe.Count > 0;
        q.LoopingMatches = loopingMatches;
        if (!q.AllowsLoops && q.CouldSuppressLoops) {
          q.Candidates = safe;
          q.RejectedCandidates.AddRange(looping);
        }

        if (looping.Count > 0) {
          foundloop = true;
        }
      }
      return foundloop;
    }

    bool RewriteMatchingLoop() {
      if (expr is QuantifierExpr) {
        QuantifierExpr quantifier = (QuantifierExpr)expr;
        var l = new List<QuantifierWithTriggers>();
        List<Expression> splits = new List<Expression>();
        bool rewritten = false;
        foreach (var q in quantifiers) {
          if (TriggerUtils.NeedsAutoTriggers(q.quantifier) && TriggerUtils.WantsMatchingLoopRewrite(q.quantifier)) {
            var matchingLoopRewriter = new MatchingLoopRewriter();
            var qq = matchingLoopRewriter.RewriteMatchingLoops(q);
            splits.Add(qq);
            l.Add(new QuantifierWithTriggers(qq));
            rewritten = true;
          } else {
            // don't rewrite the quantifier if we are not auto generate triggers.
            // This is because rewriting introduces new boundvars and will cause
            // user provided triggers not mention all boundvars
            splits.Add(q.quantifier);
            l.Add(q);
          }
        }
        if (rewritten) {
          quantifier.SplitQuantifier = splits;
          quantifiers = l;
          return true;
        }
      }
      return false;
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

    internal class QuantifierGroup {
      internal QuantifierWithTriggers quantifier;
      internal List<ComprehensionExpr> expressions;

      public QuantifierGroup(QuantifierWithTriggers q, List<ComprehensionExpr> expressions) {
        this.quantifier = q;
        this.expressions = expressions;
      }
    }

    // group split quantifier by what triggers they got, and merged them back into one quantifier.
    private void CombineSplitQuantifier() {
      if (quantifiers.Count > 1) {
        List<QuantifierGroup> groups = new List<QuantifierGroup>();
        groups.Add(new QuantifierGroup(quantifiers[0], new List<ComprehensionExpr> { quantifiers[0].quantifier }));
        for (int i = 1; i < quantifiers.Count; i++) {
          bool found = false;
          for (int j = 0; j < groups.Count; j++) {
            if (HasSameTriggers(quantifiers[i], groups[j].quantifier)) {
              // belong to the same group
              groups[j].expressions.Add(quantifiers[i].quantifier);
              found = true;
              break;
            }
          }
          if (!found) {
            // start a new group
            groups.Add(new QuantifierGroup(quantifiers[i], new List<ComprehensionExpr> { quantifiers[i].quantifier }));
          }
        }
        if (groups.Count == quantifiers.Count) {
          // have the same number of splits, so no splits are combined.
          return;
        }
        // merge expressions in each group back to one quantifier.
        List<QuantifierWithTriggers> list = new List<QuantifierWithTriggers>();
        List<Expression> splits = new List<Expression>();
        foreach (var group in groups) {
          QuantifierWithTriggers q = group.quantifier;
          if (q.quantifier is ForallExpr) {
            ForallExpr quantifier = (ForallExpr)q.quantifier;
            Expression expr = QuantifiersToExpression(quantifier.tok, BinaryExpr.ResolvedOpcode.And, group.expressions);
            q.quantifier = new ForallExpr(quantifier.tok, quantifier.RangeToken, quantifier.BoundVars, quantifier.Range, expr, TriggerUtils.CopyAttributes(quantifier.Attributes)) { Type = quantifier.Type, Bounds = quantifier.Bounds };
          } else if (q.quantifier is ExistsExpr) {
            ExistsExpr quantifier = (ExistsExpr)q.quantifier;
            Expression expr = QuantifiersToExpression(quantifier.tok, BinaryExpr.ResolvedOpcode.Or, group.expressions);
            q.quantifier = new ExistsExpr(quantifier.tok, quantifier.RangeToken, quantifier.BoundVars, quantifier.Range, expr, TriggerUtils.CopyAttributes(quantifier.Attributes)) { Type = quantifier.Type, Bounds = quantifier.Bounds };
          }
          list.Add(q);
          splits.Add(q.quantifier);
        }
        this.quantifiers = list;
        Contract.Assert(this.expr is QuantifierExpr); // only QuantifierExpr has SplitQuantifier
        ((QuantifierExpr)this.expr).SplitQuantifier = splits;
      }
    }

    private bool HasSameTriggers(QuantifierWithTriggers one, QuantifierWithTriggers other) {
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

    private void CommitOne(QuantifierWithTriggers q, bool addHeader) {
      var errorLevel = ErrorLevel.Info;
      var msg = new StringBuilder();
      var indent = addHeader ? "  " : "";
      bool suppressWarnings = Attributes.Contains(q.quantifier.Attributes, "nowarn");
      var reportingToken = q.quantifier.tok;
      // If there is only one subexpression, we discard the nested token information.
      if (reportingToken is NestedToken nestedToken && !addHeader) {
        reportingToken = nestedToken.Outer;
      }

      void FirstLetterCapitalOnNestedToken() {
        if (reportingToken is NestedToken nestToken && nestToken.Message != null && nestToken.Message.Length > 1) {
          reportingToken = new NestedToken(nestToken.Outer, nestToken.Inner,
            char.ToUpper(nestToken.Message[0]) + nestToken.Message.Substring(1));
        }
      }

      if (!TriggerUtils.NeedsAutoTriggers(q.quantifier)) { // NOTE: split and autotriggers attributes are passed down to Boogie
        var extraMsg = TriggerUtils.WantsAutoTriggers(q.quantifier) ? "" : " Note that {:autotriggers false} can cause instabilities. Consider using {:nowarn}, {:matchingloop} (not great either), or a manual trigger instead.";
        msg.AppendFormat("Not generating triggers for \"{0}\".{1}", Printer.ExprToString(q.quantifier.Term), extraMsg).AppendLine();
      } else {
        if (addHeader) {
          msg.AppendFormat("For expression \"{0}\":", Printer.ExprToString(q.quantifier.Term)).AppendLine();
        }

        foreach (var candidate in q.Candidates) {
          q.quantifier.Attributes = new Attributes("trigger", candidate.Terms.Select(t => t.Expr).ToList(), q.quantifier.Attributes);
        }

        AddTriggersToMessage("Selected triggers:", q.Candidates, msg, indent);
        AddTriggersToMessage("Rejected triggers:", q.RejectedCandidates, msg, indent, true);

#if QUANTIFIER_WARNINGS
        var WARN_TAG = DafnyOptions.O.UnicodeOutput ? "⚠ " : @"/!\ ";
        var WARN_TAG_OVERRIDE = suppressWarnings ? "(Suppressed warning) " : WARN_TAG;
        var WARN_LEVEL = suppressWarnings ? ErrorLevel.Info : ErrorLevel.Warning;
        var WARN = indent + WARN_TAG_OVERRIDE;
        if (!q.CandidateTerms.Any()) {
          errorLevel = WARN_LEVEL;
          msg.Append(WARN).AppendLine("No terms found to trigger on.");
          FirstLetterCapitalOnNestedToken();
        } else if (!q.Candidates.Any()) {
          errorLevel = WARN_LEVEL;
          msg.Append(WARN).AppendLine("No trigger covering all quantified variables found.");
          FirstLetterCapitalOnNestedToken();
        } else if (!q.CouldSuppressLoops && !q.AllowsLoops) {
          errorLevel = WARN_LEVEL;
          msg.Append(WARN).AppendLine("Suppressing loops would leave this expression without triggers.");
          FirstLetterCapitalOnNestedToken();
        } else if (suppressWarnings) {
          errorLevel = ErrorLevel.Warning;
          msg.Append(indent).Append(WARN_TAG).AppendLine("There is no warning here to suppress.");
          FirstLetterCapitalOnNestedToken();
        }
#endif
      }

      if (msg.Length > 0 && !Attributes.Contains(q.quantifier.Attributes, "auto_generated")) {
        var msgStr = msg.ToString().TrimEnd("\r\n ".ToCharArray());
        reporter.Message(MessageSource.Rewriter, errorLevel, null, reportingToken, msgStr);
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
