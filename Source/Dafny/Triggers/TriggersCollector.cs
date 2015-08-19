using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;
using System.Diagnostics;

namespace Microsoft.Dafny.Triggers {
  struct TriggerCandidate {
    internal Expression Expr { get; set; }
    internal ISet<IVariable> Variables { get; set; }

    public override string ToString() {
      return Printer.ExprToString(Expr);
    }
  }

  class MultiTriggerCandidate {
    internal List<TriggerCandidate> terms { get; set; }

    internal MultiTriggerCandidate(List<TriggerCandidate> candidates) {
      this.terms = candidates;
    }

    internal bool MentionsAll(List<BoundVar> vars) {
      return vars.All(x => terms.Any(candidate => candidate.Variables.Contains(x)));
    }

    public override string ToString() {
      return String.Join(", ", terms);
    }

    public String AsDafnyAttributeString(bool wrap = true, bool includeTags = false) {
      var repr = terms.MapConcat(t => Printer.ExprToString(t.Expr), ", ");
      if (wrap) {
        repr = "{:trigger " + repr + "}";
      }
      return repr;
    }
  }

  class TriggerAnnotation {
    internal bool IsTriggerKiller;
    internal ISet<IVariable> Variables;
    internal readonly List<TriggerCandidate> PrivateTerms;
    internal readonly List<TriggerCandidate> ExportedTerms;

    internal TriggerAnnotation(bool IsTriggerKiller, IEnumerable<IVariable> Variables,
                                IEnumerable<TriggerCandidate> AllCandidates, IEnumerable<TriggerCandidate> PrivateCandidates = null) {
      this.IsTriggerKiller = IsTriggerKiller;
      this.Variables = new HashSet<IVariable>(Variables);

      this.PrivateTerms = new List<TriggerCandidate>(PrivateCandidates == null ? Enumerable.Empty<TriggerCandidate>() : PrivateCandidates);
      this.ExportedTerms = new List<TriggerCandidate>(AllCandidates == null ? Enumerable.Empty<TriggerCandidate>() : AllCandidates.Except(this.PrivateTerms));
    }

    public override string ToString() {
      StringBuilder sb = new StringBuilder();
      string indent = "  {0}", nindent = "\n  - {0}", subindent = "\n    * {0}";

      sb.AppendFormat(indent, IsTriggerKiller);

      sb.AppendFormat(nindent, "Variables:");
      foreach (var bv in Variables) {
        sb.AppendFormat(subindent, bv.Name);
      }

      sb.AppendFormat(nindent, "Exported candidates:");
      foreach (var candidate in ExportedTerms) {
        sb.AppendFormat(subindent, candidate);
      }

      if (PrivateTerms.Any()) {
        sb.AppendFormat(nindent, "Private candidates:");
        foreach (var candidate in PrivateTerms) {
          sb.AppendFormat(subindent, candidate);
        }
      }

      return sb.ToString();
    }
  }

  public class TriggersCollector {
    Dictionary<Expression, TriggerAnnotation> cache;

    private static TriggersCollector instance = new TriggersCollector();

    private TriggersCollector() {
      this.cache = new Dictionary<Expression, TriggerAnnotation>();
    }

    private T ReduceAnnotatedSubExpressions<T>(Expression expr, T seed, Func<TriggerAnnotation, T> map, Func<T, T, T> reduce) {
      return expr.SubExpressions.Select(e => map(Annotate(e)))
                                .Aggregate(seed, (acc, e) => reduce(acc, e));
    }

    private List<TriggerCandidate> CollectExportedCandidates(Expression expr) {
      return ReduceAnnotatedSubExpressions<List<TriggerCandidate>>(expr, new List<TriggerCandidate>(), a => a.ExportedTerms, TriggerUtils.MergeAlterFirst);
    }

    private ISet<IVariable> CollectVariables(Expression expr) {
      return ReduceAnnotatedSubExpressions(expr, new HashSet<IVariable>(), a => a.Variables, TriggerUtils.MergeAlterFirst);
    }

    private bool CollectIsKiller(Expression expr) {
      return ReduceAnnotatedSubExpressions(expr, false, a => a.IsTriggerKiller, (a, b) => a || b);
    }

    private IEnumerable<TriggerCandidate> OnlyPrivateCandidates(List<TriggerCandidate> candidates, IEnumerable<IVariable> privateVars) {
      return candidates.Where(c => privateVars.Intersect(c.Variables).Any()); //TODO Check perf
    }

    private TriggerAnnotation Annotate(Expression expr) {
      TriggerAnnotation cached;
      if (cache.TryGetValue(expr, out cached)) {
        return cached;
      }

      expr.SubExpressions.Iter(e => Annotate(e));

      TriggerAnnotation annotation; // TODO: Using ApplySuffix fixes the unresolved members problem in GenericSort
      if (expr is FunctionCallExpr || expr is SeqSelectExpr || expr is MemberSelectExpr || expr is OldExpr ||
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
      } else if (expr is ConcreteSyntaxExpression ||
                 expr is LiteralExpr ||
                 expr is OldExpr ||
                 expr is ThisExpr ||
                 expr is BoxingCastExpr ||
                 expr is DatatypeValue ||
                 expr is SeqDisplayExpr) { //FIXME what abvout other display expressions?
        annotation = AnnotateOther(expr, false);
      } else {
        annotation = AnnotateOther(expr, true);
      }

      TriggerUtils.DebugTriggers("{0} ({1})\n{2}", Printer.ExprToString(expr), expr.GetType(), annotation);
      cache[expr] = annotation;
      return annotation;
    }

    private BinaryExpr.ResolvedOpcode RemoveNotInBinaryExprIn(BinaryExpr.ResolvedOpcode opcode) {
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

    private Expression CleanupExpr(Expression expr, out bool isKiller) {
      isKiller = false;

      if (!(expr is BinaryExpr)) {
        return expr;
      }

      var bexpr = expr as BinaryExpr;

      BinaryExpr new_expr = bexpr;
      if (bexpr.Op == BinaryExpr.Opcode.NotIn) {
        new_expr = new BinaryExpr(bexpr.tok, BinaryExpr.Opcode.In, bexpr.E0, bexpr.E1);
        new_expr.ResolvedOp = RemoveNotInBinaryExprIn(bexpr.ResolvedOp);
        new_expr.Type = bexpr.Type;
      }

      Expression returned_expr = new_expr;
      if (new_expr.ResolvedOp == BinaryExpr.ResolvedOpcode.InMultiSet) {
        returned_expr = new SeqSelectExpr(new_expr.tok, true, new_expr.E1, new_expr.E0, null);
        returned_expr.Type = bexpr.Type;
        isKiller = true; // [a in s] becomes [s[a] > 0], which is a trigger killer
      }

      return returned_expr;
    }

    private TriggerAnnotation AnnotatePotentialCandidate(Expression expr) {
      bool expr_is_killer = false;
      var new_expr = CleanupExpr(expr, out expr_is_killer);
      var new_candidate = new TriggerCandidate { Expr = new_expr, Variables = CollectVariables(expr) };

      List<TriggerCandidate> collected_candidates = CollectExportedCandidates(expr);
      var children_contain_killers = CollectIsKiller(expr);

      if (!children_contain_killers) {
        // Add only if the children are not killers; the head has been cleaned up into non-killer form
        collected_candidates.Add(new_candidate);
      }

      // This new node is a killer if its children were killers, or if it's non-cleaned-up head is a killer
      return new TriggerAnnotation(children_contain_killers || expr_is_killer, new_candidate.Variables, collected_candidates);
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
      annotation.ExportedTerms.RemoveAll(candidate => expr.SubExpressions.Contains(candidate.Expr));
      return annotation;
    }

    private TriggerAnnotation AnnotateQuantifierOrLetExpr(Expression expr, IEnumerable<BoundVar> boundVars) {
      var candidates = CollectExportedCandidates(expr);
      return new TriggerAnnotation(true, CollectVariables(expr), candidates, OnlyPrivateCandidates(candidates, boundVars));
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

    private TriggerAnnotation AnnotateOther(Expression expr, bool isTriggerKiller) {
      return new TriggerAnnotation(isTriggerKiller || CollectIsKiller(expr), CollectVariables(expr), CollectExportedCandidates(expr));
    }

    // FIXME document that this will contain duplicates
    internal static List<TriggerCandidate> CollectTriggers(QuantifierExpr quantifier) {
      // TODO could check for existing triggers and return that instead, but that require a bit of work to extract the expressions
      return instance.Annotate(quantifier).PrivateTerms;
    }

    internal static bool IsTriggerKiller(Expression expr) {
      return instance.Annotate(expr).IsTriggerKiller;
    }
  }
}
