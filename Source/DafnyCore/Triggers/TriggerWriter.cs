using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny.Triggers;

class TriggerWriter {
  public ComprehensionExpr Comprehension { get; set; }
  public List<TriggerTerm> CandidateTerms { get; set; }
  public List<TriggerCandidate> Candidates { get; set; }
  private List<TriggerCandidate> RejectedCandidates { get; }
  private List<TriggerMatch> loopingMatches;

  private bool AllowsLoops => TriggerUtils.AllowsMatchingLoops(Comprehension);
  private bool CouldSuppressLoops { get; set; }

  internal TriggerWriter(ComprehensionExpr comprehension) {
    this.Comprehension = comprehension;
    this.RejectedCandidates = new List<TriggerCandidate>();
  }

  internal void TrimInvalidTriggers() {
    Contract.Requires(CandidateTerms != null);
    Contract.Requires(Candidates != null);
    Candidates = TriggerUtils.Filter(Candidates, tr => tr, (tr, _) => tr.MentionsAll(Comprehension.BoundVars), (tr, _) => { }).ToList();
  }

  public bool DetectAndFilterLoopingCandidates(ErrorReporter reporter) {
    var looping = new List<TriggerCandidate>();
    var loopingMatches = new List<TriggerMatch>();

    var nonLoopingCandidates = new List<TriggerCandidate>();
    foreach (var candidate in Candidates) {
      var loopingSubterms = candidate.LoopingSubterms(Comprehension, reporter.Options).ToList();
      if (loopingSubterms.Any()) {
        looping.Add(candidate);
        loopingMatches = loopingSubterms.ToList();
        candidate.Annotation = "may loop with " + string.Join(", ", 
          loopingSubterms.Select(t => "\"" + Printer.ExprToString(reporter.Options, t.OriginalExpr) + "\""));
      } else {
        nonLoopingCandidates.Add(candidate);
      }
    }

    CouldSuppressLoops = nonLoopingCandidates.Count > 0;
    this.loopingMatches = loopingMatches;
    if (!AllowsLoops && CouldSuppressLoops) {
      Candidates = nonLoopingCandidates;
      RejectedCandidates.AddRange(looping);
    }

    return looping.Count > 0;
  }

  public bool RewriteMatchingLoop(ErrorReporter reporter, ModuleDefinition module) {
    if (TriggerUtils.NeedsAutoTriggers(Comprehension) && TriggerUtils.WantsMatchingLoopRewrite(Comprehension)) {
      var triggersCollector = new TriggersCollector(new (), 
        reporter.Options, module);
      // rewrite quantifier to avoid matching loops
      // before:
      //    assert forall i :: 0 <= i < a.Length-1 ==> a[i] <= a[i+1];
      // after:
      //    assert forall i,j :: j == i+1 ==> 0 <= i < a.Length-1 ==> a[i] <= a[j];
      var substMap = new List<Tuple<Expression, IdentifierExpr>>();
      foreach (var triggerMatch in loopingMatches) {
        var e = triggerMatch.OriginalExpr;
        if (triggersCollector.IsPotentialTriggerCandidate(e) && triggersCollector.IsTriggerKiller(e)) {
          foreach (var sub in e.SubExpressions) {
            if (triggersCollector.IsTriggerKiller(sub) && (!triggersCollector.IsPotentialTriggerCandidate(sub))) {
              var entry = substMap.Find(x => ExprExtensions.ExpressionEq(sub, x.Item1));
              if (entry == null) {
                var newBv = new BoundVar(sub.tok, "_t#" + substMap.Count, sub.Type);
                var ie = new IdentifierExpr(sub.tok, newBv.Name);
                ie.Var = newBv;
                ie.Type = newBv.Type;
                substMap.Add(new Tuple<Expression, IdentifierExpr>(sub, ie));
              }
            }
          }
        }
      }

      var expr = (QuantifierExpr)Comprehension;
      if (substMap.Count > 0) {
        var s = new ExprSubstituter(substMap);
        expr = s.Substitute(Comprehension) as QuantifierExpr;
      } else {
        // make a copy of the expr
        if (expr is ForallExpr) {
          expr = new ForallExpr(expr.tok, expr.RangeToken, expr.BoundVars, expr.Range, expr.Term, 
            TriggerUtils.CopyAttributes(expr.Attributes)) { Type = expr.Type, Bounds = expr.Bounds };
        } else {
          expr = new ExistsExpr(expr.tok, expr.RangeToken, expr.BoundVars, expr.Range, expr.Term, 
            TriggerUtils.CopyAttributes(expr.Attributes)) { Type = expr.Type, Bounds = expr.Bounds };
        }
      }
      var qq = expr;
      
      Comprehension = qq;
      Candidates.Clear();
      CandidateTerms.Clear();
      loopingMatches.Clear();
      RejectedCandidates.Clear();
      return true;
    }

    // don't rewrite the quantifier if we are not auto generate triggers.
    // This is because rewriting introduces new boundvars and will cause
    // user provided triggers not mention all boundvars
    return false;
  }

  // TODO Check whether this makes verification faster
  public void FilterStrongCandidates()
  {
    var newCandidates = new List<TriggerCandidate>();
    foreach (var candidate in Candidates) {
      var weakerCandidates = Candidates.Where(candidate.IsStrongerThan).ToList();
      if (weakerCandidates.Any()) {
        RejectedCandidates.Add(candidate);
        candidate.Annotation = "more specific than " + string.Join(", ", weakerCandidates);
      } else {
        newCandidates.Add(candidate);
      }
    }
    Candidates = newCandidates;
  }

  public void CommitTrigger(ErrorReporter errorReporter, SystemModuleManager systemModuleManager) {
    bool suppressWarnings = Attributes.Contains(Comprehension.Attributes, "nowarn");
    var reportingToken = Comprehension.Tok;
    var warningLevel = suppressWarnings ? ErrorLevel.Info : ErrorLevel.Warning;

    if (TriggerUtils.WantsAutoTriggers(Comprehension)) {
      // NOTE: split and autotriggers attributes are passed down to Boogie
      errorReporter.Message(MessageSource.Rewriter, warningLevel, null, reportingToken, "Note that {:autotriggers false} can cause instabilities. Consider using {:nowarn}, {:matchingloop} (not great either), or a manual trigger instead.");
    }

    if (TriggerUtils.NeedsAutoTriggers(Comprehension)) {
      AddTriggerAttribute(systemModuleManager);
        
      errorReporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, reportingToken, 
        $"Selected triggers: {String.Join(", ", Candidates)}");
      errorReporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, reportingToken,
        $"Rejected triggers: {String.Join("\n", RejectedCandidates)}");

      if (!CandidateTerms.Any() || !Candidates.Any()) {
        errorReporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, reportingToken,
          $"Could not find a trigger for this quantifier. Without a trigger, the quantifier may heavily worsen verification performance. For more information, see the section on quantifier triggers in the reference manual.");
      }
      if (!CouldSuppressLoops && !AllowsLoops) {
        errorLevel = warningLevel;
        msg.Append(WARN).AppendLine("Suppressing loops would leave this expression without triggers.");
        FirstLetterCapitalOnNestedToken();
      } 
      //
      //   errorLevel = warningLevel;
      //   msg.Append(WARN).AppendLine(
      //     "this quantifier may not be effectively used by the verifier; you may experience brittleness, possibly right away or possibly down the road; for more information, see 'ineffective quantifiers' in the reference manual [expert info: no trigger for bound variable 'x']");
      //   FirstLetterCapitalOnNestedToken();
      // } else if (!quantifier.Candidates.Any()) {
      //   errorLevel = warningLevel;
      //   msg.Append(WARN).AppendLine("No trigger covering all quantified variables found.");
      //   FirstLetterCapitalOnNestedToken();
      // } else else if (suppressWarnings) {
      //   errorLevel = ErrorLevel.Warning;
      //   msg.Append(indent).Append(WARN_TAG).AppendLine("There is no warning here to suppress.");
      //   FirstLetterCapitalOnNestedToken();
      // }
      //
      // if (msg.Length > 0 && !Attributes.Contains(quantifier.quantifier.Attributes, "auto_generated")) {
      //   var msgStr = msg.ToString().TrimEnd("\r\n ".ToCharArray());
      //   reporter.Message(MessageSource.Rewriter, errorLevel, null, reportingToken, msgStr);
      // }
    }
  }
  
  private void AddTriggerAttribute(SystemModuleManager systemModuleManager)
  {
    foreach (var candidate in Candidates) {
      Comprehension.Attributes = new Attributes("trigger",
        candidate.Terms.ConvertAll(t => Expression.WrapAsParsedStructureIfNecessary(t.Expr, systemModuleManager)),
        Comprehension.Attributes);
    }
  }
}