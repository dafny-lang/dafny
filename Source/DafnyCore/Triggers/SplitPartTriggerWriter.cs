using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny.Triggers;

/// <summary>
/// Determines the triggers for a comprehension that resulted from splitting another one
/// </summary>
class SplitPartTriggerWriter {
  public ComprehensionExpr Comprehension { get; set; }
  public List<TriggerTerm> CandidateTerms { get; set; }
  public List<TriggerCandidate> Candidates { get; set; }
  private List<TriggerCandidate> RejectedCandidates { get; }
  public List<Tuple<Expression, IdentifierExpr>> NamedExpressions { get; }
  private List<TriggerMatch> loopingMatches;
  // The terms of the loops that the matching-loop rewrite could not name, as they mention variables bound inside the
  // quantifier, with these variables
  private List<(Expression Term, List<IVariable> Inner)> unnamed = [];

  private bool AllowsLoops {
    get {
      // This is different from nowarn: it won't remove loops at all, even if another trigger is available.
      return Attributes.Contains(Comprehension.Attributes, "matchingloop");
    }
  }

  private bool CouldSuppressLoops { get; set; }

  internal SplitPartTriggerWriter(ComprehensionExpr comprehension) {
    this.Comprehension = comprehension;
    this.RejectedCandidates = [];
    this.NamedExpressions = [];
  }

  internal void TrimInvalidTriggers() {
    Contract.Requires(CandidateTerms != null);
    Contract.Requires(Candidates != null);
    Candidates = Candidates.Where(tr => tr.MentionsAll(Comprehension.BoundVars)).ToList();
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
    if (!NeedsAutoTriggers() || !WantsMatchingLoopRewrite()) {
      return false;
    }

    var triggersCollector = new TriggersCollector(new(),
      reporter.Options, module);
    // rewrite quantifier to avoid matching loops
    // before:
    //    assert forall i :: 0 <= i < a.Length-1 ==> a[i] <= a[i+1];
    // after, in the verifier's translation:
    //    assert forall i,j {:trigger a[i], a[j]} :: j == i+1 ==> 0 <= i < a.Length-1 ==> a[i] <= a[j];
    var substMap = new List<Tuple<Expression, IdentifierExpr>>();
    foreach (var triggerMatch in loopingMatches) {
      var e = triggerMatch.OriginalExpr;
      if (triggersCollector.IsPotentialTriggerCandidate(e) && triggersCollector.IsTriggerKiller(e)) {
        foreach (var sub in e.SubExpressions) {
          if (triggersCollector.IsTriggerKiller(sub) && (!triggersCollector.IsPotentialTriggerCandidate(sub))) {
            var entry = substMap.Find(x => ExprExtensions.ExpressionEq(sub, x.Item1));
            if (entry == null) {
              var newBv = new BoundVar(sub.Origin, "_t#" + substMap.Count, sub.Type);
              var ie = new IdentifierExpr(sub.Origin, newBv.Name) { Var = newBv, Type = newBv.Type };
              substMap.Add(new Tuple<Expression, IdentifierExpr>(sub, ie));
            }
          }
        }
      }
    }

    var expr = (QuantifierExpr)Comprehension;
    if (substMap.Count > 0) {
      // The copy only selects the triggers. The verifier binds a variable to each term in its translation of the part as
      // written.
      var s = new NamedTermSubstituter(expr, substMap, reporter.Options);
      var range = expr.Range == null ? null : s.Substitute(expr.Range);
      var term = s.Substitute(expr.Term);
      var used = substMap.FindAll(x => s.Used.Contains(x.Item2));
      unnamed = s.Unnamed;
      NamedExpressions.AddRange(used);
      expr = Bind(expr, range, term, used);
    } else {
      expr = Bind(expr, expr.Range, expr.Term, []);
    }
    var qq = expr;

    Comprehension = qq;
    Candidates.Clear();
    CandidateTerms.Clear();
    loopingMatches.Clear();
    RejectedCandidates.Clear();
    return true;

    // don't rewrite the quantifier if we are not auto generate triggers.
    // This is because rewriting introduces new boundvars and will cause
    // user provided triggers not mention all boundvars
  }

  /// <summary>
  /// A copy of the quantifier with the range and term given that also binds each name's variable to its term, as the
  /// verifier's translation does, which keeps the term's own subterms as candidates
  /// </summary>
  private static QuantifierExpr Bind(QuantifierExpr quantifier, Expression range, Expression term,
    List<Tuple<Expression, IdentifierExpr>> names) {
    foreach (var (named, variable) in names) {
      var definition = new BinaryExpr(quantifier.Origin, BinaryExpr.ResolvedOpcode.EqCommon, variable, named);
      range = range == null ? definition : new BinaryExpr(quantifier.Origin, BinaryExpr.ResolvedOpcode.And, definition, range);
    }
    var boundVars = quantifier.BoundVars.Concat(names.Select(x => (BoundVar)x.Item2.Var)).ToList();
    var bounds = quantifier.Bounds?.Concat(names.Select(x => (BoundedPool)new ExactBoundedPool(x.Item1))).ToList();
    var attributes = TriggerUtils.CopyAttributes(quantifier.Attributes);
    return quantifier is ForallExpr
      ? new ForallExpr(quantifier.Origin, boundVars, range, term, attributes) { Type = quantifier.Type, Bounds = bounds }
      : new ExistsExpr(quantifier.Origin, boundVars, range, term, attributes) { Type = quantifier.Type, Bounds = bounds };
  }

  /// <summary>
  /// Replaces each term that mentions no variable bound inside the part with its variable. A term that reads the heap is
  /// not replaced inside an "old" or a lambda, where it reads another heap and the verifier does not replace it either.
  /// </summary>
  private class NamedTermSubstituter : Substituter {
    // Each term that the substituter replaces, with its variable and whether it reads the heap
    private readonly List<(Expression Term, IdentifierExpr Variable, bool ReadsHeap)> terms = [];
    private bool otherHeap;
    public readonly HashSet<IdentifierExpr> Used = [];
    // The other terms, with the variables bound inside the part that they mention
    public readonly List<(Expression Term, List<IVariable> Inner)> Unnamed = [];

    public NamedTermSubstituter(QuantifierExpr part, List<Tuple<Expression, IdentifierExpr>> substMap, DafnyOptions options)
      : base(null, new Dictionary<IVariable, Expression>(), new Dictionary<TypeParameter, Type>()) {
      var scope = FreeVariablesUtil.ComputeFreeVariables(options, part);
      scope.UnionWith(part.BoundVars);
      foreach (var (term, variable) in substMap) {
        var termVariables = new HashSet<IVariable>();
        var readsHeap = false;
        FreeVariablesUtil.ComputeFreeVariables(options, term, termVariables, ref readsHeap);
        if (termVariables.IsSubsetOf(scope)) {
          terms.Add((term, variable, readsHeap));
        } else {
          Unnamed.Add((term, termVariables.Except(scope).ToList()));
        }
      }
    }

    public override Expression Substitute(Expression expr) {
      foreach (var (term, variable, readsHeap) in terms) {
        if (!(readsHeap && otherHeap) && ExprExtensions.ExpressionEq(expr, term)) {
          Used.Add(variable);
          return variable;
        }
      }
      if (expr is not (OldExpr or LambdaExpr)) {
        return base.Substitute(expr);
      }
      var outer = otherHeap;
      otherHeap = true;
      var result = base.Substitute(expr);
      otherHeap = outer;
      return result;
    }
  }

  // TODO Check whether this makes verification faster
  public void FilterStrongCandidates() {
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

  public void CommitTrigger(ErrorReporter errorReporter, int? splitPartIndex, SystemModuleManager systemModuleManager) {
    bool suppressWarnings = Attributes.Contains(Comprehension.Attributes, "nowarn");
    var reportingToken = Comprehension.Origin;
    var warningLevel = suppressWarnings ? ErrorLevel.Info : ErrorLevel.Warning;

    if (!WantsAutoTriggers()) {
      // NOTE: split and autotriggers attributes are passed down to Boogie
      errorReporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, reportingToken,
        "The attribute {:autotriggers false} may cause brittle verification. " +
        "It's better to remove this attribute, or as a second option, manually define a trigger using {:trigger}. " +
        "For more information, see the section on quantifier instantiation rules in the reference manual.");
    }

    if (!NeedsAutoTriggers()) {
      DisableEmptyTriggers(Comprehension.Attributes, "trigger");
      return;
    }

    AddTriggerAttribute(systemModuleManager);

    if (Attributes.Contains(Comprehension.Attributes, "auto_generated")) {
      return;
    }

    string InfoFirstLineEnd(int count) {
      return count < 2 ? " " : "\n  ";
    }

    var messages = new List<string>();
    if (splitPartIndex != null) {
      messages.Add($"Part #{splitPartIndex} is '{Comprehension.Term}'");
    }
    if (Candidates.Any()) {
      var subst = Util.Comma("", NamedExpressions, pair => $" where {pair.Item2} := {pair.Item1}");
      messages.Add($"Selected triggers:{InfoFirstLineEnd(Candidates.Count)}{string.Join(", ", Candidates)}{subst}");
    }
    if (RejectedCandidates.Any()) {
      messages.Add($"Rejected triggers:{InfoFirstLineEnd(RejectedCandidates.Count)}{string.Join("\n  ", RejectedCandidates)}");
    }

    if (messages.Any()) {
      errorReporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, reportingToken, string.Join("\n", messages));
    }

    const string hint = "To silence this warning, add an explicit trigger using the {:trigger} attribute. " +
                        "For more information, see the section on quantifier instantiation rules in the reference manual.";
    if (!CandidateTerms.Any() || !Candidates.Any()) {
      if (Attributes.Contains(Comprehension.Attributes, "_delayTriggerWarning")) {
        // Just record the fact that no auto-trigger was found
        Comprehension.Attributes = new Attributes("_noAutoTriggerFound", new List<Expression>(), Comprehension.Attributes);
      } else {
        errorReporter.Message(MessageSource.Rewriter, warningLevel, null, reportingToken,
          "Could not find a trigger for this quantifier. Without a trigger, the quantifier may cause brittle verification. " + hint);
      }
    } else if (!CouldSuppressLoops && !AllowsLoops) {
      errorReporter.Message(MessageSource.Rewriter, warningLevel, null, reportingToken,
        "Triggers were added to this quantifier that may introduce matching loops, which may cause brittle verification. " +
        (HowToBreakLoop(errorReporter.Options) ?? hint));
    }
  }

  /// <summary>
  /// How to break a loop through a term that the rewrite could not name as it mentions the variables of a quantifier
  /// inside this one, if each instance of this one instantiates that quantifier, so that the solver gives these
  /// variables no new values, or else null. If that quantifier also has conjuncts without the term, the advice moves
  /// those with it to a quantifier of their own, as the triggers of all would need a term for the new variable.
  /// </summary>
  private string HowToBreakLoop(DafnyOptions options) {
    foreach (var (term, inner) in unnamed) {
      if (Binder(((QuantifierExpr)Comprehension).Term, inner[0], Comprehension is ForallExpr) is not { } binder ||
          !inner.All(variable => binder.BoundVars.Contains(variable))) {
        continue;
      }
      var termText = Printer.ExprToString(options, term);
      var innerText = string.Join(", ", inner.Select(variable => variable.Name));
      var used = Comprehension.AllSubExpressions(false, false).OfType<IdentifierExpr>().Select(e => e.Name)
        .Concat(binder.BoundVars.Select(variable => variable.Name)).ToHashSet();
      var name = Enumerable.Range(0, used.Count + 1).Select(i => i == 0 ? "t" : $"t{i}").First(n => !used.Contains(n));
      var example = $"{(binder is ForallExpr ? "forall" : "exists")} " +
                    $"{string.Join(", ", binder.BoundVars.Select(variable => variable.Name))}, {name} | " +
                    $"{(binder.Range == null ? "" : "... && ")}{name} == {termText}";
      var conjuncts = QuantifierSplitter.Conjuncts(binder).ConvertAll(part => part.Term);
      var how = conjuncts.TrueForAll(conjunct =>
        conjunct.AllSubExpressions(false, false).Any(e => ExprExtensions.ExpressionEq(e, term)))
        ? $"replace '{termText}' with a new variable bound alongside '{innerText}'"
        : $"move the {(binder is ForallExpr ? "conjuncts" : "disjuncts")} with '{termText}' to a separate quantifier over " +
          $"'{innerText}', and replace the term there with a new variable";
      return $"To break the loop, {how}, as in '{example}', or add {{:nowarn}} to silence this warning. " +
             "For more information, see the section on quantifier instantiation rules in the reference manual.";
    }
    return null;
  }

  // The quantifier that binds the variable, if expr reaches it only through conjunctions, disjunctions, implications,
  // negations and quantifiers of the given kind, which negations and antecedents flip
  private static QuantifierExpr Binder(Expression expr, IVariable variable, bool forall) {
    return expr.Resolved switch {
      QuantifierExpr quantifier when quantifier is ForallExpr != forall => null,
      QuantifierExpr quantifier => quantifier.BoundVars.Contains(variable) ? quantifier : Binder(quantifier.Term, variable, forall),
      UnaryOpExpr { ResolvedOp: UnaryOpExpr.ResolvedOpcode.BoolNot } not => Binder(not.E, variable, !forall),
      BinaryExpr { ResolvedOp: BinaryExpr.ResolvedOpcode.And or BinaryExpr.ResolvedOpcode.Or } binary =>
        Binder(binary.E0, variable, forall) ?? Binder(binary.E1, variable, forall),
      BinaryExpr { ResolvedOp: BinaryExpr.ResolvedOpcode.Imp } binary =>
        Binder(binary.E0, variable, !forall) ?? Binder(binary.E1, variable, forall),
      _ => null
    };
  }

  public static void DisableEmptyTriggers(Attributes attribs, String attrName) {
    foreach (var attr in attribs.AsEnumerable()) {
      if (attr.Name == attrName && attr.Args.Count == 0) {
        // Remove an empty trigger attribute, so it does not crash Boogie,
        // and effectively becomes a way to silence a Dafny warning
        attr.Name = $"deleted-{attrName}";
      }
    }
  }

  private void AddTriggerAttribute(SystemModuleManager systemModuleManager) {
    // A trigger has each named term where the copy has its variable. Only a translation that binds a variable to each
    // term can use such a trigger, so it is internal, as the terms are
    var terms = new Substituter(null, NamedExpressions.ToDictionary(x => x.Item2.Var, x => x.Item1),
      new Dictionary<TypeParameter, Type>());
    foreach (var candidate in Candidates) {
      Comprehension.Attributes = new Attributes(NamedExpressions.Count == 0 ? "trigger" : "_trigger",
        candidate.Terms.ConvertAll(t => Expression.WrapAsParsedStructureIfNecessary(
          NamedExpressions.Count == 0 ? t.Expr : terms.Substitute(t.Expr), systemModuleManager)),
        Comprehension.Attributes);
    }
    if (Candidates.Count != 0 && NamedExpressions.Count != 0) {
      Comprehension.Attributes = new Attributes("_named", NamedExpressions.ConvertAll(x => x.Item1), Comprehension.Attributes);
    }
  }

  private bool WantsAutoTriggers() {
    bool wantsAutoTriggers = true;
    return !Attributes.ContainsBool(Comprehension.Attributes, "autotriggers", ref wantsAutoTriggers) || wantsAutoTriggers;
  }

  private bool NeedsAutoTriggers() {
    return !Attributes.Contains(Comprehension.Attributes, "trigger") && !Attributes.Contains(Comprehension.Attributes, "_trigger") &&
           WantsAutoTriggers();
  }

  bool WantsMatchingLoopRewrite() {
    bool wantsMatchingLoopRewrite = true;
    return (!Attributes.ContainsBool(Comprehension.Attributes, "matchinglooprewrite", ref wantsMatchingLoopRewrite) || wantsMatchingLoopRewrite) && WantsAutoTriggers();
  }
}