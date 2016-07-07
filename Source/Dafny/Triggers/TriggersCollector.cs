using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;
using System.Diagnostics;

namespace Microsoft.Dafny.Triggers {
  class TriggerTerm {
    internal Expression Expr { get; set; }
    internal Expression OriginalExpr { get; set; }
    internal ISet<IVariable> Variables { get; set; }
    internal IEnumerable<BoundVar> BoundVars {
      get {
        return Variables.Select(v => v as BoundVar).Where(v => v != null);
      }
    }

    public override string ToString() {
      return Printer.ExprToString(Expr); 
      // NOTE: Using OriginalExpr here could cause some confusion: 
      // for example, {a !in b} is a binary expression, yielding 
      // trigger {a in b}. Saying the trigger is a !in b would be 
      // rather misleading.
    }

    internal enum TermComparison {
      SameStrength = 0, Stronger = 1, NotStronger = -1
    }

    internal TermComparison CompareTo(TriggerTerm other) {
      if (this == other) {
        return TermComparison.SameStrength;
      } else if (Expr.AllSubExpressions(true, true).Any(other.Expr.ExpressionEq)) {
        return TermComparison.Stronger;
      } else {
        return TermComparison.NotStronger;
      }
    }

    internal static bool Eq(TriggerTerm t1, TriggerTerm t2) {
      return ExprExtensions.ExpressionEq(t1.Expr, t2.Expr);
    }

    internal bool IsTranslatedToFunctionCall() {
      return (TriggersCollector.TranslateToFunctionCall(this.Expr)) ? true : false;
    }

  }

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

    internal string Repr { get { return String.Join(", ", Terms); } }

    public override string ToString() {
      return "{" + Repr + "}" + (String.IsNullOrWhiteSpace(Annotation) ? "" : " (" + Annotation + ")");
    }

    internal IEnumerable<TriggerMatch> LoopingSubterms(ComprehensionExpr quantifier) {
      Contract.Requires(!(quantifier is QuantifierExpr) || ((QuantifierExpr)quantifier).SplitQuantifier == null); // Don't call this on a quantifier with a Split clause: it's not a real quantifier
      var matchingSubterms = this.MatchingSubterms(quantifier);
      var boundVars = new HashSet<BoundVar>(quantifier.BoundVars);
      return matchingSubterms.Where(tm => tm.CouldCauseLoops(Terms, boundVars));
    }

    internal List<TriggerMatch> MatchingSubterms(ComprehensionExpr quantifier) {
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

  internal class TriggerAnnotation {
    internal bool IsTriggerKiller;
    internal ISet<IVariable> Variables;
    internal readonly List<TriggerTerm> PrivateTerms;
    internal readonly List<TriggerTerm> ExportedTerms;

    internal TriggerAnnotation(bool IsTriggerKiller, IEnumerable<IVariable> Variables, IEnumerable<TriggerTerm> AllTerms, IEnumerable<TriggerTerm> PrivateTerms = null) {
      this.IsTriggerKiller = IsTriggerKiller;
      this.Variables = new HashSet<IVariable>(Variables);
      this.PrivateTerms = new List<TriggerTerm>(PrivateTerms == null ? Enumerable.Empty<TriggerTerm>() : PrivateTerms);
      this.ExportedTerms = new List<TriggerTerm>(AllTerms == null ? Enumerable.Empty<TriggerTerm>() : AllTerms.Except(this.PrivateTerms));
    }

    public override string ToString() {
      StringBuilder sb = new StringBuilder();
      string indent = "  {0}", nindent = "\n  - {0}", subindent = "\n    * {0}";

      sb.AppendFormat(indent, IsTriggerKiller);

      sb.AppendFormat(nindent, "Variables:");
      foreach (var bv in Variables) {
        sb.AppendFormat(subindent, bv.Name);
      }

      sb.AppendFormat(nindent, "Exported terms:");
      foreach (var term in ExportedTerms) {
        sb.AppendFormat(subindent, term);
      }

      if (PrivateTerms.Any()) {
        sb.AppendFormat(nindent, "Private terms:");
        foreach (var term in PrivateTerms) {
          sb.AppendFormat(subindent, term);
        }
      }

      return sb.ToString();
    }
  }

  internal class TriggerAnnotationsCache {
    public readonly HashSet<Expression> exprsInOldContext;
    public readonly Dictionary<Expression, TriggerAnnotation> annotations;

    /// <summary>
    /// For certain operations, the TriggersCollector class needs to know whether 
    /// an particular expression is under an old(...) wrapper. This is in particular 
    /// true for generating trigger terms (but it is not for checking wehter something 
    /// is a trigger killer, so passing an empty set here for that case would be fine.
    /// </summary>
    public TriggerAnnotationsCache(HashSet<Expression> exprsInOldContext) {
      this.exprsInOldContext = exprsInOldContext;
      annotations = new Dictionary<Expression, TriggerAnnotation>();
    }
  }

  internal class TriggersCollector {
    TriggerAnnotationsCache cache;

    internal TriggersCollector(HashSet<Expression> exprsInOldContext) {
      this.cache = new TriggerAnnotationsCache(exprsInOldContext);
    }

    private T ReduceAnnotatedSubExpressions<T>(Expression expr, T seed, Func<TriggerAnnotation, T> map, Func<T, T, T> reduce) {
      return expr.SubExpressions.Select(e => map(Annotate(e)))
                                .Aggregate(seed, (acc, e) => reduce(acc, e));
    }

    private List<TriggerTerm> CollectExportedCandidates(Expression expr) {
      return ReduceAnnotatedSubExpressions<List<TriggerTerm>>(expr, new List<TriggerTerm>(), a => a.ExportedTerms, TriggerUtils.MergeAlterFirst);
    }

    private ISet<IVariable> CollectVariables(Expression expr) {
      return ReduceAnnotatedSubExpressions(expr, new HashSet<IVariable>(), a => a.Variables, TriggerUtils.MergeAlterFirst);
    }

    private bool CollectIsKiller(Expression expr) {
      return ReduceAnnotatedSubExpressions(expr, false, a => a.IsTriggerKiller, (a, b) => a || b);
    }

    private IEnumerable<TriggerTerm> OnlyPrivateCandidates(List<TriggerTerm> terms, IEnumerable<IVariable> privateVars) {
      return terms.Where(c => privateVars.Intersect(c.Variables).Any()); //TODO Check perf
    }

    private TriggerAnnotation Annotate(Expression expr) {
      TriggerAnnotation cached;
      if (cache.annotations.TryGetValue(expr, out cached)) {
        return cached;
      }

      expr.SubExpressions.Iter(e => Annotate(e));

      TriggerAnnotation annotation; // TODO: Using ApplySuffix fixes the unresolved members problem in GenericSort
      if (expr is FunctionCallExpr || 
          expr is SeqSelectExpr || 
          expr is MultiSelectExpr || 
          expr is MemberSelectExpr || 
          expr is OldExpr || 
          expr is ApplyExpr || 
          expr is DisplayExpression ||
          TranslateToFunctionCall(expr) ||
          (expr is UnaryOpExpr && (((UnaryOpExpr)expr).Op == UnaryOpExpr.Opcode.Cardinality)) || // FIXME || ((UnaryOpExpr)expr).Op == UnaryOpExpr.Opcode.Fresh doesn't work, as fresh is a pretty tricky predicate when it's not about datatypes. See translator.cs:10944
          (expr is BinaryExpr && (((BinaryExpr)expr).Op == BinaryExpr.Opcode.NotIn || ((BinaryExpr)expr).Op == BinaryExpr.Opcode.In))) {
        annotation = AnnotatePotentialCandidate(expr);
      } else if (expr is QuantifierExpr) {
          annotation = AnnotateQuantifier((QuantifierExpr)expr);
      } else if (expr is LetExpr) {
        annotation = AnnotateLetExpr((LetExpr)expr);
      } else if (expr is IdentifierExpr) {
        annotation = AnnotateIdentifier((IdentifierExpr)expr);
      } else if (expr is ApplySuffix) {
        annotation = AnnotateApplySuffix((ApplySuffix)expr);
      } else if (expr is ComprehensionExpr) {
        annotation = AnnotateComprehensionExpr((ComprehensionExpr)expr);
      } else if (expr is ConcreteSyntaxExpression ||
                 expr is LiteralExpr ||
                 expr is OldExpr ||
                 expr is ThisExpr ||
                 expr is BoxingCastExpr ||
                 expr is DatatypeValue ||
                 expr is MultiSetFormingExpr) {
        annotation = AnnotateOther(expr, false);
      } else {
        annotation = AnnotateOther(expr, true);
      }

      TriggerUtils.DebugTriggers("{0} ({1})\n{2}", Printer.ExprToString(expr), expr.GetType(), annotation);
      cache.annotations[expr] = annotation;
      return annotation;
    }

    // math operations can be turned into a Boogie-level function as in the 
    // case with /noNLarith.
    public static bool TranslateToFunctionCall(Expression expr) {
      if (!(expr is BinaryExpr)) {
        return false;
      }
      BinaryExpr e = (BinaryExpr) expr;
      bool isReal = e.E0.Type.IsNumericBased(Type.NumericPersuation.Real);
      switch (e.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.Add:
        case BinaryExpr.ResolvedOpcode.Sub:
        case BinaryExpr.ResolvedOpcode.Mul:
        case BinaryExpr.ResolvedOpcode.Div:
        case BinaryExpr.ResolvedOpcode.Mod:
          if (!isReal && DafnyOptions.O.DisableNLarith) {
            return true;
          }
          break;
      }
      return false;
    }
    private TriggerAnnotation AnnotatePotentialCandidate(Expression expr) {
      bool expr_is_killer = false;
      var new_expr = TriggerUtils.MaybeWrapInOld(TriggerUtils.PrepareExprForInclusionInTrigger(expr, out expr_is_killer), cache.exprsInOldContext.Contains(expr));
      var new_term = new TriggerTerm { Expr = new_expr, OriginalExpr = expr, Variables = CollectVariables(expr) };

      List<TriggerTerm> collected_terms = CollectExportedCandidates(expr);
      var children_contain_killers = CollectIsKiller(expr);

      if (!children_contain_killers) {
        // Add only if the children are not killers; the head has been cleaned up into non-killer form
        collected_terms.Add(new_term);
      }

      // This new node is a killer if its children were killers, or if it's non-cleaned-up head is a killer
      return new TriggerAnnotation(children_contain_killers || expr_is_killer, new_term.Variables, collected_terms);
    }

    private TriggerAnnotation AnnotateApplySuffix(ApplySuffix expr) {
      // This is a bit tricky. A funcall node is generally meaningful as a trigger candidate, 
      // but when it's part of an ApplySuffix the function call itself may not resolve properly
      // when the second round of resolving is done after modules are duplicated.
      // Thus first we annotate expr and create a trigger candidate, and then we remove the 
      // candidate matching its direct subexpression if needed. Note that function calls are not the 
      // only possible child here; there can be DatatypeValue nodes, for example (see vstte2012/Combinators.dfy).
      var annotation = AnnotatePotentialCandidate(expr);
      // Comparing by reference is fine here. Using sets could yield a small speedup
      annotation.ExportedTerms.RemoveAll(term => expr.SubExpressions.Contains(term.Expr));
      return annotation;
    }

    private TriggerAnnotation AnnotateQuantifierOrLetExpr(Expression expr, IEnumerable<BoundVar> boundVars) {
      var terms = CollectExportedCandidates(expr);
      return new TriggerAnnotation(true, CollectVariables(expr), terms, OnlyPrivateCandidates(terms, boundVars));
    }

    private TriggerAnnotation AnnotateQuantifier(QuantifierExpr expr) {
      return AnnotateQuantifierOrLetExpr(expr, expr.BoundVars);
    }

    private TriggerAnnotation AnnotateLetExpr(LetExpr expr) {
      return AnnotateQuantifierOrLetExpr(expr, expr.BoundVars);
    }

    private TriggerAnnotation AnnotateIdentifier(IdentifierExpr expr) {
      return new TriggerAnnotation(false, Enumerable.Repeat(expr.Var, 1), null);
    }

    private TriggerAnnotation AnnotateComprehensionExpr(ComprehensionExpr expr) {
      var terms = CollectExportedCandidates(expr);
      return new TriggerAnnotation(true, CollectVariables(expr), terms,  OnlyPrivateCandidates(terms, expr.BoundVars));
    }

    private TriggerAnnotation AnnotateOther(Expression expr, bool isTriggerKiller) {
      return new TriggerAnnotation(isTriggerKiller || CollectIsKiller(expr), CollectVariables(expr), CollectExportedCandidates(expr));
    }

    /// <summary>
    /// Collect terms in the body of the subexpressions of the argument that look like quantifiers. The results of this function can contain duplicate terms.
    /// </summary>
    internal List<TriggerTerm> CollectTriggers(ComprehensionExpr quantifier) {
      Contract.Requires(!(quantifier is QuantifierExpr) || ((QuantifierExpr)quantifier).SplitQuantifier == null); // Don't call this on a quantifier with a Split clause: it's not a real quantifier
      // NOTE: We could check for existing trigger attributes and return that instead
      return Annotate(quantifier).PrivateTerms;
    }

    internal bool IsTriggerKiller(Expression expr) {
      return Annotate(expr).IsTriggerKiller;
    }
  }
}
