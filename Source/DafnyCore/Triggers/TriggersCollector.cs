// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

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
    public readonly Dictionary<Expression, HashSet<OldExpr>> exprsInOldContext;
    public readonly Dictionary<Expression, TriggerAnnotation> annotations;

    /// <summary>
    /// For certain operations, the TriggersCollector class needs to know whether
    /// a particular expression is under an old(...) wrapper. This is in particular
    /// true for generating trigger terms (but it is not for checking whether something
    /// is a trigger killer, so passing an empty set here for that case would be fine.
    /// </summary>
    public TriggerAnnotationsCache(Dictionary<Expression, HashSet<OldExpr>> exprsInOldContext) {
      this.exprsInOldContext = exprsInOldContext;
      annotations = new Dictionary<Expression, TriggerAnnotation>();
    }
  }

  internal class TriggersCollector {
    TriggerAnnotationsCache cache;

    internal TriggersCollector(Dictionary<Expression, HashSet<OldExpr>> exprsInOldContext) {
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
      return ReduceAnnotatedSubExpressions<ISet<IVariable>>(expr, new HashSet<IVariable>(), a => a.Variables, TriggerUtils.MergeAlterFirst);
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

      TriggerAnnotation annotation = null; // TODO: Using ApplySuffix fixes the unresolved members problem in GenericSort

      if (expr is LetExpr) {
        var le = (LetExpr)expr;
        if (le.LHSs.All(p => p.Var != null) && le.Exact) {
          // Inline the let expression before doing trigger selection.
          annotation = Annotate(Translator.InlineLet(le));
        }
      }

      if (annotation == null) {
        expr.SubExpressions.Iter(e => Annotate(e));

        if (IsPotentialTriggerCandidate(expr)) {
          annotation = AnnotatePotentialCandidate(expr);
        } else if (expr is QuantifierExpr) {
          annotation = AnnotateQuantifier((QuantifierExpr)expr);
        } else if (expr is LetExpr) {
          annotation = AnnotateLetExpr((LetExpr)expr);
        } else if (expr is IdentifierExpr) {
          annotation = AnnotateIdentifier((IdentifierExpr)expr);
        } else if (expr is ApplySuffix) {
          annotation = AnnotateApplySuffix((ApplySuffix)expr);
        } else if (expr is MatchExpr) {
          annotation = AnnotateMatchExpr((MatchExpr)expr);
        } else if (expr is NestedMatchExpr nestedMatchExpr) {
          annotation = AnnotateNestedMatchExpr(nestedMatchExpr);
        } else if (expr is ComprehensionExpr) {
          annotation = AnnotateComprehensionExpr((ComprehensionExpr)expr);
        } else if (expr is ConcreteSyntaxExpression ||
                   expr is LiteralExpr ||
                   expr is ThisExpr ||
                   expr is BoxingCastExpr ||
                   expr is MultiSetFormingExpr ||
                   expr is SeqConstructionExpr) {
          annotation = AnnotateOther(expr, false);
        } else {
          annotation = AnnotateOther(expr, true);
        }
      }

      TriggerUtils.DebugTriggers("{0} ({1})\n{2}", Printer.ExprToString(expr), expr.GetType(), annotation);
      cache.annotations[expr] = annotation;
      return annotation;
    }

    public static bool IsPotentialTriggerCandidate(Expression expr) {
      if (expr is FunctionCallExpr ||
          expr is SeqSelectExpr ||
          expr is MultiSelectExpr ||
          expr is MemberSelectExpr ||
          (expr is OldExpr { Useless: false }) ||
          expr is ApplyExpr ||
          expr is DisplayExpression ||
          expr is MapDisplayExpr ||
          expr is DatatypeValue ||
          TranslateToFunctionCall(expr)) {
        return true;
      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        if ((e.Op == BinaryExpr.Opcode.NotIn || e.Op == BinaryExpr.Opcode.In) && !Translator.ExpressionTranslator.RewriteInExpr(e.E1, false)) {
          return true;
        } else if (CandidateCollectionOperation(e)) {
          return true;
        } else if (e.E0.Type.IsBigOrdinalType &&
                   (e.ResolvedOp == BinaryExpr.ResolvedOpcode.Lt || e.ResolvedOp == BinaryExpr.ResolvedOpcode.LessThanLimit || e.ResolvedOp == BinaryExpr.ResolvedOpcode.Gt)) {
          return true;
        } else {
          return false;
        }
      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        return e.Op == UnaryOpExpr.Opcode.Cardinality;  // FIXME || e.Op == UnaryOpExpr.Opcode.Fresh doesn't work, as fresh is a pretty tricky predicate when it's not about datatypes. See translator.cs:10944
      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        return e.ToType.IsBigOrdinalType;
      } else {
        return false;
      }
    }

    // math operations can be turned into a Boogie-level function as in the
    // case with /noNLarith.
    public static bool TranslateToFunctionCall(Expression expr) {
      if (!(expr is BinaryExpr)) {
        return false;
      }
      BinaryExpr e = (BinaryExpr)expr;
      bool isReal = e.E0.Type.IsNumericBased(Type.NumericPersuasion.Real);
      switch (e.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.Add:
        case BinaryExpr.ResolvedOpcode.Sub:
          if (!isReal && !e.E0.Type.IsBitVectorType && !e.E0.Type.IsBigOrdinalType && DafnyOptions.O.DisableNLarith) {
            return true;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
        case BinaryExpr.ResolvedOpcode.Div:
        case BinaryExpr.ResolvedOpcode.Mod:
          if (!isReal && !e.E0.Type.IsBitVectorType && !e.E0.Type.IsBigOrdinalType) {
            if (DafnyOptions.O.DisableNLarith || (DafnyOptions.O.ArithMode != 0 && DafnyOptions.O.ArithMode != 3)) {
              return true;
            }
          }
          break;
      }
      return false;
    }

    static bool CandidateCollectionOperation(BinaryExpr binExpr) {
      Contract.Requires(binExpr != null);
      var type = binExpr.E0.Type.AsCollectionType;
      if (type == null) {
        return false;
      }
      if (type is SetType) {
        switch (binExpr.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.Union:
          case BinaryExpr.ResolvedOpcode.Intersection:
          case BinaryExpr.ResolvedOpcode.SetDifference:
          case BinaryExpr.ResolvedOpcode.ProperSubset:
          case BinaryExpr.ResolvedOpcode.Subset:
          case BinaryExpr.ResolvedOpcode.Superset:
          case BinaryExpr.ResolvedOpcode.ProperSuperset:
            return true;
          default:
            break;
        }
      } else if (type is MultiSetType) {
        switch (binExpr.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          case BinaryExpr.ResolvedOpcode.MultiSubset:
          case BinaryExpr.ResolvedOpcode.MultiSuperset:
          case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
            return true;
          default:
            break;
        }
      } else if (type is SeqType) {
        switch (binExpr.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.Concat:
            return true;
          default:
            break;
        }
      } else if (type is MapType) {
        switch (binExpr.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.MapMerge:
          case BinaryExpr.ResolvedOpcode.MapSubtraction:
            return true;
          default:
            break;
        }
      }
      return false;
    }

    private TriggerAnnotation AnnotatePotentialCandidate(Expression expr) {
      bool expr_is_killer = false;
      HashSet<OldExpr> oldExprSet;
      if (cache.exprsInOldContext.TryGetValue(expr, out oldExprSet)) {
        // oldExpr has been set to the value found
      } else {
        oldExprSet = null;
      }
      var new_exprs = TriggerUtils.MaybeWrapInOld(TriggerUtils.PrepareExprForInclusionInTrigger(expr, out expr_is_killer), oldExprSet);
      // We expect there to be at least one "new_exprs".
      // We also expect that the computation of new_term.Variables, collected_terms, and children_contain_killers will be the
      // same for each of the "new_exprs".
      // Therefore, we use the values of these variables from the last iteration in the expression that is ultimately returned.
      TriggerTerm new_term = null;
      List<TriggerTerm> collected_terms = null;
      var children_contain_killers = false;
      foreach (var new_expr in new_exprs) {
        new_term = new TriggerTerm { Expr = new_expr, OriginalExpr = expr, Variables = CollectVariables(expr) };

        collected_terms = CollectExportedCandidates(expr);
        children_contain_killers = CollectIsKiller(expr);

        if (!children_contain_killers) {
          // Add only if the children are not killers; the head has been cleaned up into non-killer form
          collected_terms.Add(new_term);
        }
      }
      Contract.Assert(new_term != null);  // this checks our assumption that "new_exprs" contains at least one value.

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
      return new TriggerAnnotation(true, CollectVariables(expr), terms, OnlyPrivateCandidates(terms, expr.BoundVars));
    }

    private TriggerAnnotation AnnotateNestedMatchExpr(NestedMatchExpr expr) {
      var candidateTerms = CollectExportedCandidates(expr);
      // collects that argument boundvar of matchcaseexpr
      var variables = expr.Cases.SelectMany(e => e.Pat.DescendantsAndSelf).
        OfType<IdPattern>().Select(id => id.BoundVar).Where(b => b != null).ToList();
      // remove terms that mentions argument boundvar of matchcaseexpr
      var terms = candidateTerms.Where(term => variables.Any(x => !term.Variables.Contains(x))).ToList();
      return new TriggerAnnotation(true, CollectVariables(expr), terms);
    }

    private TriggerAnnotation AnnotateMatchExpr(MatchExpr expr) {
      var pts = CollectExportedCandidates(expr);
      // collects that argument boundvar of matchcaseexpr
      var variables = expr.Cases.Select(e => e.Arguments).
        Aggregate(new List<BoundVar>(), (acc, e) => TriggerUtils.MergeAlterFirst(acc, e));
      // remove terms that mentions argument boundvar of matchcaseexpr
      var terms = new List<TriggerTerm>();
      foreach (var term in pts) {
        if (!(variables.All(x => term.Variables.Contains(x)))) {
          terms.Add(term);
        }
      }
      return new TriggerAnnotation(true, CollectVariables(expr), terms);
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
