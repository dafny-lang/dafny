#define DEBUG_AUTO_TRIGGERS
#define THROW_UNSUPPORTED_COMPARISONS

using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using System.Diagnostics.Contracts;
using System.Text;
using System.Diagnostics;

//FIXME No LitInts in triggers
//FIXME Generated triggers should be _triggers, and if a predicate is called with something that can't be a trigger head we shouldn't inline it (see .\Test\dafny2\SnapshotableTrees.dfy)
//FIXME: When scoring, do not consider old(x) to be higher than x.

/* High level note: There are really two processes going on here. One is finding quantifiers; 
 * the other is walking the subtree corresponding to each quantifier, and finding trigger candidates.
 * These two processes are interleaved, because we can look for trigger candidates as we look for 
 * quantifiers. Since the visitor starts from the bottom of the tree, the recursive annotation 
 * procedure never causes deep recursion; every call it makes hits the cache that has been built 
 * during the visiting of lower level nodes.
 * 
 * Note also that it wouldn't be enough to just use the recursive procedure: it doesn't visit 
 * statements, for example.
 */

namespace Microsoft.Dafny {
  class TriggerCandidate { // TODO Hashing is broken (duplicates can pop up)
    internal Expression Expr;
    internal ISet<IVariable> Variables;
    internal Expression[] PotentialMatchingLoops;

    public override string ToString() {
      return Printer.ExprToString(Expr);
    }
  }
  
  struct MultiTriggerCandidate {
    internal ISet<TriggerCandidate> Candidates;
    internal double Score;

    public override string ToString() {
      return String.Format("[{0:G2}] {1}", Score, String.Join(", ", Candidates));
    }
  }

  class TriggerAnnotation {
    internal bool IsTriggerKiller;
    internal ISet<IVariable> Variables;
    internal readonly HashSet<TriggerCandidate> PrivateCandidates;
    internal readonly HashSet<TriggerCandidate> ExportedCandidates;

    internal TriggerAnnotation(bool IsTriggerKiller, IEnumerable<IVariable> Variables, 
                               IEnumerable<TriggerCandidate> AllCandidates, IEnumerable<TriggerCandidate> PrivateCandidates = null) {
      this.IsTriggerKiller = IsTriggerKiller;
      this.Variables = new HashSet<IVariable>(Variables);

      this.ExportedCandidates = new HashSet<TriggerCandidate>(AllCandidates == null ? Enumerable.Empty<TriggerCandidate>() : AllCandidates);
      this.PrivateCandidates = new HashSet<TriggerCandidate>(PrivateCandidates == null ? Enumerable.Empty<TriggerCandidate>() : PrivateCandidates);
      this.ExportedCandidates.ExceptWith(this.PrivateCandidates);
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
      foreach (var candidate in ExportedCandidates) {
        sb.AppendFormat(subindent, candidate);
      }

      if (PrivateCandidates.Any()) {
        sb.AppendFormat(nindent, "Private candidates:");
        foreach (var candidate in PrivateCandidates) {
          sb.AppendFormat(subindent, candidate);
        }
      }

      return sb.ToString();
    }
  }

  public class TriggerGenerator : BottomUpVisitor {
    List<QuantifierExpr> quantifiers;
    Dictionary<Expression, TriggerAnnotation> annotations;

    Resolver Resolver;

    private TriggerGenerator(Resolver resolver) {
      Contract.Requires(Resolver != null);
      this.quantifiers = new List<QuantifierExpr>();
      this.annotations = new Dictionary<Expression, TriggerAnnotation>();
      this.Resolver = resolver;
    }

    private ISet<T> MergeAlterFirst<T>(ISet<T> a, ISet<T> b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      a.UnionWith(b);
      return a;
    }

    private ISet<T> WithOneExtraElement<T>(ISet<T> set, T elem) {
      Contract.Requires(set != null);
      set.Add(elem);
      return set;
    }

    private T ReduceAnnotatedSubExpressions<T>(Expression expr, T seed, Func<TriggerAnnotation, T> map, Func<T, T, T> reduce) {
      return expr.SubExpressions.Select(e => map(Annotate(e)))
                                .Aggregate(seed, (acc, e) => reduce(acc, e));
    }

    private ISet<TriggerCandidate> CollectExportedCandidates(Expression expr) {
      return ReduceAnnotatedSubExpressions<ISet<TriggerCandidate>>(expr, new HashSet<TriggerCandidate>(), a => a.ExportedCandidates, MergeAlterFirst);
    }

    private ISet<IVariable> CollectVariables(Expression expr) {
      return ReduceAnnotatedSubExpressions(expr, new HashSet<IVariable>(), a => a.Variables, MergeAlterFirst);
    }

    private bool CollectIsKiller(Expression expr) {
      return ReduceAnnotatedSubExpressions(expr, false, a => a.IsTriggerKiller, (a, b) => a || b);
    }

    private IEnumerable<TriggerCandidate> OnlyPrivateCandidates(ISet<TriggerCandidate> candidates, IEnumerable<IVariable> privateVars) {
      return candidates.Where(c => privateVars.Intersect(c.Variables).Any()); //TODO Check perf
    }

    private TriggerAnnotation Annotate(Expression expr) {
      TriggerAnnotation cached;
      if (annotations.TryGetValue(expr, out cached)) {
        return cached;
      }

      expr.SubExpressions.Iter(e => Annotate(e)); //NOTE: These values are all cached

      TriggerAnnotation annotation; // TODO: Using ApplySuffix fixes the unresolved members problem in GenericSort
      if (expr is FunctionCallExpr || expr is SeqSelectExpr || expr is MemberSelectExpr || expr is OldExpr ||
          (expr is UnaryOpExpr && (((UnaryOpExpr)expr).Op == UnaryOpExpr.Opcode.Cardinality)) || // FIXME || ((UnaryOpExpr)expr).Op == UnaryOpExpr.Opcode.Fresh oesn't work, as fresh is a pretty tricky predicate when it's not about datatypes. See translator.cs:10944
          (expr is BinaryExpr  && (((BinaryExpr)expr).Op == BinaryExpr.Opcode.NotIn || ((BinaryExpr)expr).Op == BinaryExpr.Opcode.In))) {
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
                 expr is DatatypeValue) {
        annotation = AnnotateOther(expr, false);
      } else {
        annotation = AnnotateOther(expr, true);
      }

      DebugTriggers("{0} ({1})\n{2}", Printer.ExprToString(expr), expr.GetType(), annotation);
      annotations[expr] = annotation;
      return annotation;
    }

    [Conditional("DEBUG_AUTO_TRIGGERS")]
    private static void DebugTriggers(string format, params object[] more) {
      Console.Error.WriteLine(format, more);
    }

    private BinaryExpr.ResolvedOpcode RemoveNotInBinaryExprIn(BinaryExpr.ResolvedOpcode opcode) {
      switch(opcode) {
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

      ISet<TriggerCandidate> collected_candidates = CollectExportedCandidates(expr);
      var children_contain_killers = CollectIsKiller(expr);

      if (!children_contain_killers) {
        // Add only if the children are not killers; the head has been cleaned up into non-killer form
        collected_candidates = WithOneExtraElement(collected_candidates, new_candidate);
      }

      // This new node is a killer if its children were killers, or if it's non-cleaned-up head is a killer
      return new TriggerAnnotation(children_contain_killers || expr_is_killer, new_candidate.Variables, collected_candidates);
    }

    private TriggerAnnotation AnnotateApplySuffix(ApplySuffix expr) {
      // This is a bit tricky. A funcall node is generally meaningful as a trigger candidate, 
      // but when it's part of an ApplySuffix the function call itself may not resolve properly
      // when the second round of resolving is done after modules are duplicated.
      // Thus first we annotate expr and create a trigger candidate, and then we remove the 
      // candidate matching its direct subexpression if needed. Not that function calls are not the 
      // only possible child here; there can be DatatypeValue nodes, for example (see vstte2012/Combinators.dfy).
      var annotation = AnnotatePotentialCandidate(expr);
      annotation.ExportedCandidates.RemoveWhere(candidate => expr.SubExpressions.Contains(candidate.Expr));
      return annotation;
    }

    private TriggerAnnotation AnnotateQuantifierOrLetExpr(Expression expr, IEnumerable<BoundVar> boundVars) {
      var candidates = CollectExportedCandidates(expr);
      return new TriggerAnnotation(true, CollectVariables(expr), candidates, OnlyPrivateCandidates(candidates, boundVars));
    }

    private TriggerAnnotation AnnotateQuantifier(QuantifierExpr expr) {
      quantifiers.Add(expr);
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

    private static List<T> CopyAndAdd<T>(List<T> seq, T elem) {
      var copy = new List<T>(seq);
      copy.Add(elem);
      return copy;
    }

    private static IEnumerable<List<T>> AllSubsets<T>(IList<T> source, int offset) {
      if (offset >= source.Count) {
        yield return new List<T>();
        yield break;
      }

      foreach (var subset in AllSubsets<T>(source, offset + 1)) {
        yield return CopyAndAdd(subset, source[offset]);
        yield return new List<T>(subset);
      }
    }

    private static IEnumerable<ISet<T>> AllSubsets<T>(IEnumerable<T> source) {
      List<T> all = new List<T>(source);
      foreach (var subset in AllSubsets(all, 0)) {
        yield return new HashSet<T>(subset);
      }
    }

    private static bool MentionsAll(ISet<TriggerCandidate> multiCandidate, List<BoundVar> vars) {
      return vars.All(x => multiCandidate.Any(candidate => candidate.Variables.Contains(x))); //TODO Perfs?
    }

    private static bool DefaultCandidateFilteringFunction(TriggerCandidate candidate, QuantifierExpr quantifier) {
      //FIXME this will miss rewritten expressions (CleanupExpr)
      //FIXME does PotentialMatchingLoops really need to be a field?

      return true;


      candidate.PotentialMatchingLoops = ExprExtensions.CouldCauseCycle(candidate.Expr, quantifier).ToArray(); 
      if (candidate.PotentialMatchingLoops.Any()) {
         DebugTriggers("Trigger {0} for quantifier {1} could cause a matching loop, due to terms {2}.", 
         Printer.ExprToString(candidate.Expr), Printer.ExprToString(quantifier), 
           String.Join(", ", candidate.PotentialMatchingLoops.Select(e => Printer.ExprToString(e))));
      }
      return !candidate.PotentialMatchingLoops.Any();
    }

    private static bool DefaultMultiCandidateFilteringFunction(ISet<TriggerCandidate> multiCandidate, QuantifierExpr quantifier) {
      return MentionsAll(multiCandidate, quantifier.BoundVars);
    }

    private static double DefaultMultiCandidateScoringFunction(ISet<TriggerCandidate> multi_candidates) {
      return 1;
    }

    private static IEnumerable<MultiTriggerCandidate> DefaultMultiCandidateSelectionFunction(List<MultiTriggerCandidate> multi_candidates) {
      return multi_candidates;
    }

    // CLEMENT: Make these customizable
    internal Func<TriggerCandidate, QuantifierExpr, bool> CandidateFilteringFunction = DefaultCandidateFilteringFunction;
    internal Func<ISet<TriggerCandidate>, QuantifierExpr, bool> MultiCandidateFilteringFunction = DefaultMultiCandidateFilteringFunction;
    internal Func<ISet<TriggerCandidate>, double> MultiCandidateScoringFunction = DefaultMultiCandidateScoringFunction;
    internal Func<List<MultiTriggerCandidate>, IEnumerable<MultiTriggerCandidate>> MultiCandidateSelectionFunction = DefaultMultiCandidateSelectionFunction;

    struct MultiCandidatesCollection {
      internal ISet<TriggerCandidate> AllCandidates;
      internal List<TriggerCandidate> SelectedCandidates;
      internal List<TriggerCandidate> RejectedCandidates;
      internal List<ISet<TriggerCandidate>> FilteredMultiCandidates;
      internal List<MultiTriggerCandidate> ScoredMultiCandidates;
      internal List<MultiTriggerCandidate> SelectedMultiCandidates;

      public MultiCandidatesCollection(QuantifierExpr quantifier,
        TriggerAnnotation annotation,
        Func<TriggerCandidate, QuantifierExpr, bool> CandidateFilteringFunction,
        Func<ISet<TriggerCandidate>, QuantifierExpr, bool> MultiCandidateFilteringFunction,
        Func<ISet<TriggerCandidate>, double> MultiCandidateScoringFunction,
        Func<List<MultiTriggerCandidate>, IEnumerable<MultiTriggerCandidate>> MultiCandidateSelectionFunction) {

        Contract.Requires(annotation != null);
        Contract.Requires(quantifier != null);
        Contract.Requires(CandidateFilteringFunction != null);
        Contract.Requires(MultiCandidateFilteringFunction != null);
        Contract.Requires(MultiCandidateScoringFunction != null);
        Contract.Requires(MultiCandidateSelectionFunction != null);

        AllCandidates = annotation.PrivateCandidates;
        Partition(AllCandidates, x => CandidateFilteringFunction(x, quantifier), out SelectedCandidates, out RejectedCandidates);
        FilteredMultiCandidates = AllSubsets(SelectedCandidates).Where(t => MultiCandidateFilteringFunction(t, quantifier)).ToList();
        ScoredMultiCandidates = FilteredMultiCandidates.Select(candidates => new MultiTriggerCandidate { Candidates = candidates, Score = MultiCandidateScoringFunction(candidates) }).ToList();
        SelectedMultiCandidates = MultiCandidateSelectionFunction(ScoredMultiCandidates).ToList();
      }

      private static void Partition<T>(IEnumerable<T> AllCandidates, Func<T, bool> CandidateFilteringFunction, out List<T> SelectedCandidates, out List<T> RejectedCandidates) {
        SelectedCandidates = new List<T>();
        RejectedCandidates = new List<T>();
        foreach (var c in AllCandidates) {
          (CandidateFilteringFunction(c) ? SelectedCandidates : RejectedCandidates).Add(c);
        }
      }

      internal string Warning() {
        if (AllCandidates.Count == 0) {
          return "No triggers found in the body of this quantifier.";
        } else if (SelectedCandidates.Count == 0) {
          return String.Format("No suitable triggers found. Candidate building blocks for a good trigger where [{0}], but no subset of these terms passed the initial selection stage.", String.Join(", ", SelectedCandidates));
        } else if (FilteredMultiCandidates.Count == 0) {
          return String.Format("No suitable set of triggers found. Candidate building blocks for a good trigger where [{0}], but no subset of these terms passed the subset selection stage.", String.Join(", ", SelectedCandidates));
        } else if (SelectedMultiCandidates.Count == 0) {
          return String.Format("No suitable set of triggers found. Candidates where [{0}], but none passed the final selection stage.", String.Join(", ", ScoredMultiCandidates));
        } else {
          return null;
        }
      }

      private void WriteIndented<T>(StringBuilder builder, string indent, IEnumerable<T> elements) {
        foreach (var element in elements) {
          builder.Append(indent).AppendLine(element.ToString());
        }
      }

      private void WriteListOfCandidates<T>(StringBuilder builder, string indent, IEnumerable<T> elements) {
        if (elements.Any()) {
          builder.AppendLine();
          WriteIndented(builder, indent, elements);
        } else {
          builder.AppendLine(" (None)");
        }
      }

      public override string ToString() {
        var repr = new StringBuilder();
        var indent = "      ";
        repr.Append("    All:");
        WriteListOfCandidates(repr, indent, AllCandidates);
        repr.Append("    PreFilter:");
        WriteListOfCandidates(repr, indent, AllSubsets(AllCandidates).Select(c => String.Join(", ", c)));
        repr.Append("    Filtered:");
        WriteListOfCandidates(repr, indent, FilteredMultiCandidates.Select(c => String.Join(", ", c))); 
        repr.Append("    Scored:");
        WriteListOfCandidates(repr, indent, ScoredMultiCandidates);
        repr.Append("    Selected:");
        WriteListOfCandidates(repr, indent, SelectedMultiCandidates);
        return repr.ToString();
      }
    }

    private MultiCandidatesCollection PickMultiTriggers(QuantifierExpr quantifier) {
      var annotation = Annotate(quantifier);
      DebugTriggers("Quantifier {0}:\n{1}", Printer.ExprToString(quantifier), annotation);
      return new MultiCandidatesCollection(quantifier, annotation, CandidateFilteringFunction, MultiCandidateFilteringFunction, MultiCandidateScoringFunction, MultiCandidateSelectionFunction);
    }

    private void AddTrigger(QuantifierExpr quantifier) {
      // This call is elided when triggers debugging is disabled.
      DebugTriggers("  Final results:\n{0}", PickMultiTriggers(quantifier));

      if (quantifier.Attributes.AsEnumerable().Any(aa => aa.Name == "trigger" || aa.Name == "no_trigger")) {
        DebugTriggers("Not generating triggers for {0}", Printer.ExprToString(quantifier)); //FIXME: no_trigger is passed down to Boogie
        return;
      }

      var multi_candidates = PickMultiTriggers(quantifier);
      foreach (var multi_candidate in multi_candidates.SelectedMultiCandidates) { //TODO: error message for when no triggers found
        quantifier.Attributes = new Attributes("trigger", multi_candidate.Candidates.Select(t => t.Expr).ToList(), quantifier.Attributes);
      }

      // FIXME: Cleanup
      if (multi_candidates.RejectedCandidates.Any()) {
        var tooltip = "Rejected: " + String.Join(Environment.NewLine + "          ", multi_candidates.RejectedCandidates.Select(
          candidate => "{:trigger " + Printer.ExprToString(candidate.Expr) + "} (could loop with " + Printer.ExprToString(candidate.PotentialMatchingLoops[0]) + ")"));
        Resolver.ReportAdditionalInformation(quantifier.tok, tooltip, quantifier.tok.val.Length); //CLEMENT Check this
      }

      if (multi_candidates.SelectedMultiCandidates.Any()) {
        var tooltip = "Triggers: " + String.Join(Environment.NewLine + "          ", multi_candidates.SelectedMultiCandidates.Select(
          multi_candidate => "{:trigger " + String.Join(", ", multi_candidate.Candidates.Select(t => Printer.ExprToString(t.Expr))) + "}"));
        Resolver.ReportAdditionalInformation(quantifier.tok, tooltip, quantifier.tok.val.Length); //CLEMENT Check this
      }

      string warning = multi_candidates.Warning();
      if (warning != null) {
        // FIXME reenable Resolver.Warning(quantifier.tok, warning);
      }
    }

    private void AddTriggers_Internal() {
      foreach (var quantifier in quantifiers) {
        AddTrigger(quantifier);
      }
    }

    private void AddTriggers_Internal(Expression root) {
      Visit(root);
      AddTriggers_Internal();
    }

    private void AddTriggers_Internal(Statement root) {
      Visit(root);
      AddTriggers_Internal();
    }

    internal static void AddTriggers(Expression root, Resolver resolver) {
      if (root == null)
        return;

      DebugTriggers("== From {0} visiting expr: {1}", new StackFrame(1).GetMethod().Name, Printer.ExprToString(root));
      TriggerGenerator generator = new TriggerGenerator(resolver);
      generator.AddTriggers_Internal(root);
    }

    internal static void AddTriggers(Statement root, Resolver resolver) {
      if (root == null)
        return;

      DebugTriggers("== From {0} visiting statement: {1}", new StackFrame(1).GetMethod().Name, Printer.StatementToString(root));
      TriggerGenerator generator = new TriggerGenerator(resolver);
      generator.AddTriggers_Internal(root);
    }

    internal static void AddTriggers(IEnumerable<Expression> roots, Resolver resolver) {
      DebugTriggers("== From {0} visiting expressions: {1}", new StackFrame(1).GetMethod().Name, 
        String.Join(", ", roots.Select(root => Printer.ExprToString(root))));
      foreach (var expr in roots) {
        AddTriggers(expr, resolver);
      }
    }

    internal static void AddTriggers(IEnumerable<MaybeFreeExpression> roots, Resolver resolver) {
      DebugTriggers("== From {0} visiting expressions: {1}", new StackFrame(1).GetMethod().Name,
        String.Join(", ", roots.Select(root => Printer.ExprToString(root.E))));
      foreach (var expr in roots) {
        AddTriggers(expr.E, resolver);
      }
    }

    protected override void VisitOneExpr(Expression expr) {
      Annotate(expr);
    }
  }

  static class ExprExtensions {
    static IEnumerable<Expression> AllSubExpressions(this Expression expr, bool strict = false) {
      foreach (var subexpr in expr.SubExpressions) {
        foreach (var r_subexpr in AllSubExpressions(subexpr, false)) {
          yield return r_subexpr;
        }
        yield return subexpr;
      }

      if (expr is StmtExpr) {
        foreach (var r_subexpr in AllSubExpressions(((StmtExpr)expr).S, false)) {
          yield return r_subexpr;
        }
      }

      if (!strict) {
        yield return expr;
      }
    }

    private static IEnumerable<Expression> AllSubExpressions(this Statement stmt, bool strict = false) {
      foreach (var subexpr in stmt.SubExpressions) {
        foreach (var r_subexpr in AllSubExpressions(subexpr, false)) {
          yield return r_subexpr;
        }
        yield return subexpr;
      }

      foreach (var substmt in stmt.SubStatements) {
        foreach (var r_subexpr in AllSubExpressions(substmt, false)) {
          yield return r_subexpr;
        }
      }
    }

    private static bool ExpressionEq(this Expression expr1, Expression expr2) {
      expr1 = GetResolved(expr1);
      expr2 = GetResolved(expr2);
      
      return ShallowEq_Top(expr1, expr2) && SameLists(expr1.SubExpressions, expr2.SubExpressions, (e1, e2) => ExpressionEq(e1, e2));
    }

    private static bool MatchesTrigger(this Expression expr, Expression trigger, ISet<BoundVar> holes, Dictionary<IVariable, Expression> bindings) {
      expr = GetResolved(expr);
      trigger = GetResolved(trigger);
      
      if (trigger is IdentifierExpr) {
        var var = ((IdentifierExpr)trigger).Var;

        if (holes.Contains(var)) {
          Expression existing_binding = null;
          if (bindings.TryGetValue(var, out existing_binding)) {
            return ExpressionEq(expr, existing_binding);
          } else {
            bindings[var] = expr;
            return true;
          }
        }
      }

      return ShallowEq_Top(expr, trigger) && SameLists(expr.SubExpressions, trigger.SubExpressions, (e1, e2) => MatchesTrigger(e1, e2, holes, bindings));
    }

    private static bool MatchesTrigger(this Expression expr, Expression trigger, ISet<BoundVar> holes) {
      return expr.MatchesTrigger(trigger, holes, new Dictionary<IVariable, Expression>());
    }

    internal static IEnumerable<Expression> CouldCauseCycle(Expression trigger, QuantifierExpr quantifier) { //FIXME Term or bound?
      //FIXME could be optimized by looking at the bindings instead of doing full equality
      return quantifier.Term.AllSubExpressions().Where(e => e.MatchesTrigger(trigger, new HashSet<BoundVar>(quantifier.BoundVars)) && !e.ExpressionEq(trigger));
    }

    private static bool SameLists<T>(IEnumerable<T> list1, IEnumerable<T> list2, Func<T, T, bool> comparer) {
      var it1 = list1.GetEnumerator();
      var it2 = list2.GetEnumerator();
      bool it1_has, it2_has;
      bool acc = true;

      do {
        it1_has = it1.MoveNext();
        it2_has = it2.MoveNext();

        if (it1_has == true && it2_has == true) {
          acc = acc && comparer(it1.Current, it2.Current);
        }
      } while (it1_has && it2_has);

      return it1_has == it2_has && acc;
    }

    private static bool SameNullity<T>(T x1, T x2) where T : class {
      return (x1 == null) == (x2 == null);
    }

    private static bool ShallowSameAttributes(Attributes attributes1, Attributes attributes2) {
      return SameLists(attributes1.AsEnumerable(), attributes2.AsEnumerable(), ShallowSameSingleAttribute);
    }

    private static bool ShallowSameSingleAttribute(Attributes arg1, Attributes arg2) {
      return arg1.Name == arg2.Name;
    }

    private static bool SameBoundVar(IVariable arg1, IVariable arg2) {
      return arg1 == arg2 || 
             (arg1.Name == arg2.Name &&
              arg1.CompileName == arg2.CompileName &&
              arg1.DisplayName == arg2.DisplayName &&
              arg1.UniqueName == arg2.UniqueName &&
              arg1.IsGhost == arg2.IsGhost &&
              arg1.IsMutable == arg2.IsMutable); //FIXME compare types?
    }

    private static Expression GetResolved(Expression expr) {
      if (expr is ConcreteSyntaxExpression) {
        return ((ConcreteSyntaxExpression)expr).ResolvedExpression;
      }
      return expr;
    }

    /// <summary>
    /// Compares two abstract syntax expressions, looking only at their direct members. Subexpressions and substatements are not compared.
    /// </summary>
    /// <returns></returns>
    internal static bool ShallowEq_Top(Expression expr1, Expression expr2) {
      Contract.Requires(expr1 != null);
      Contract.Requires(expr2 != null);

      // We never compare concrete expressions
      Contract.Requires(!(expr1 is ConcreteSyntaxExpression));
      Contract.Requires(!(expr2 is ConcreteSyntaxExpression));

      // CPC: Hey future editor: the following block of code is auto-generated. Just add your own cases at the end.
      //      This could be a visitor pattern, except I need to visit a pair of nodes. 
      //      It could also be implemented in each individual class. I'd have a slight preference for that.
      //      This really just wants to use double dispatch.
      if (expr1 is UnboxingCastExpr && expr2 is UnboxingCastExpr) {
        return ShallowEq((UnboxingCastExpr)expr1, (UnboxingCastExpr)expr2);
      } else if (expr1 is BoxingCastExpr && expr2 is BoxingCastExpr) {
        return ShallowEq((BoxingCastExpr)expr1, (BoxingCastExpr)expr2);
      } else if (expr1 is MatchExpr && expr2 is MatchExpr) {
        return ShallowEq((MatchExpr)expr1, (MatchExpr)expr2);
      } else if (expr1 is ITEExpr && expr2 is ITEExpr) {
        return ShallowEq((ITEExpr)expr1, (ITEExpr)expr2);
      } else if (expr1 is StmtExpr && expr2 is StmtExpr) {
        return ShallowEq((StmtExpr)expr1, (StmtExpr)expr2);
      } else if (expr1 is WildcardExpr && expr2 is WildcardExpr) {
        return ShallowEq((WildcardExpr)expr1, (WildcardExpr)expr2);
      } else if (expr1 is ComprehensionExpr && expr2 is ComprehensionExpr) {
        return ShallowEq((ComprehensionExpr)expr1, (ComprehensionExpr)expr2);
      } else if (expr1 is NamedExpr && expr2 is NamedExpr) {
        return ShallowEq((NamedExpr)expr1, (NamedExpr)expr2);
      } else if (expr1 is LetExpr && expr2 is LetExpr) {
        return ShallowEq((LetExpr)expr1, (LetExpr)expr2);
      } else if (expr1 is TernaryExpr && expr2 is TernaryExpr) {
        return ShallowEq((TernaryExpr)expr1, (TernaryExpr)expr2);
      } else if (expr1 is BinaryExpr && expr2 is BinaryExpr) {
        return ShallowEq((BinaryExpr)expr1, (BinaryExpr)expr2);
      } else if (expr1 is UnaryExpr && expr2 is UnaryExpr) {
        return ShallowEq((UnaryExpr)expr1, (UnaryExpr)expr2);
      } else if (expr1 is MultiSetFormingExpr && expr2 is MultiSetFormingExpr) {
        return ShallowEq((MultiSetFormingExpr)expr1, (MultiSetFormingExpr)expr2);
      } else if (expr1 is OldExpr && expr2 is OldExpr) {
        return ShallowEq((OldExpr)expr1, (OldExpr)expr2);
      } else if (expr1 is FunctionCallExpr && expr2 is FunctionCallExpr) {
        return ShallowEq((FunctionCallExpr)expr1, (FunctionCallExpr)expr2);
      } else if (expr1 is ApplyExpr && expr2 is ApplyExpr) {
        return ShallowEq((ApplyExpr)expr1, (ApplyExpr)expr2);
      } else if (expr1 is SeqUpdateExpr && expr2 is SeqUpdateExpr) {
        return ShallowEq((SeqUpdateExpr)expr1, (SeqUpdateExpr)expr2);
      } else if (expr1 is MultiSelectExpr && expr2 is MultiSelectExpr) {
        return ShallowEq((MultiSelectExpr)expr1, (MultiSelectExpr)expr2);
      } else if (expr1 is SeqSelectExpr && expr2 is SeqSelectExpr) {
        return ShallowEq((SeqSelectExpr)expr1, (SeqSelectExpr)expr2);
      } else if (expr1 is MemberSelectExpr && expr2 is MemberSelectExpr) {
        return ShallowEq((MemberSelectExpr)expr1, (MemberSelectExpr)expr2);
      } else if (expr1 is MapDisplayExpr && expr2 is MapDisplayExpr) {
        return ShallowEq((MapDisplayExpr)expr1, (MapDisplayExpr)expr2);
      } else if (expr1 is DisplayExpression && expr2 is DisplayExpression) {
        return ShallowEq((DisplayExpression)expr1, (DisplayExpression)expr2);
      } else if (expr1 is IdentifierExpr && expr2 is IdentifierExpr) {
        return ShallowEq((IdentifierExpr)expr1, (IdentifierExpr)expr2);
      } else if (expr1 is ThisExpr && expr2 is ThisExpr) {
        return ShallowEq((ThisExpr)expr1, (ThisExpr)expr2);
      } else if (expr1 is DatatypeValue && expr2 is DatatypeValue) {
        return ShallowEq((DatatypeValue)expr1, (DatatypeValue)expr2);
      } else if (expr1 is LiteralExpr && expr2 is LiteralExpr) {
        return ShallowEq((LiteralExpr)expr1, (LiteralExpr)expr2);
      } else {
        // If this assertion fail, then a new abstract AST node was probably introduced but not registered here.
        Contract.Assert(expr1.GetType() != expr2.GetType());
        return false;
      }
    }

    private static bool ShallowEq(UnboxingCastExpr expr1, UnboxingCastExpr expr2) {
      Contract.Requires(false);
      throw new InvalidOperationException();
    }

    private static bool ShallowEq(BoxingCastExpr expr1, BoxingCastExpr expr2) {
      return expr1.FromType == expr2.FromType &&
             expr1.ToType == expr2.ToType;
    }

    private static bool ShallowEq(MatchExpr expr1, MatchExpr expr2) {
      return true;
    }

    private static bool ShallowEq(ITEExpr expr1, ITEExpr expr2) {
      return true;
    }

    private static bool ShallowEq(StmtExpr expr1, StmtExpr expr2) {
#if THROW_UNSUPPORTED_COMPARISONS
      Contract.Assume(false); // This kind of expression never appears in a trigger
      throw new NotImplementedException();
#else
      return expr1.S == expr2.S;
#endif
    }

    private static bool ShallowEq(WildcardExpr expr1, WildcardExpr expr2) {
      return true;
    }

    private static bool ShallowEq(LambdaExpr expr1, LambdaExpr expr2) {
#if THROW_UNSUPPORTED_COMPARISONS
      Contract.Assume(false); // This kind of expression never appears in a trigger
      throw new NotImplementedException();
#else
      return expr1.OneShot == expr2.OneShot &&
             SameLists(expr1.Reads, expr2.Reads, SameFrameExpression);
#endif
    }

    private static bool ShallowEq(MapComprehension expr1, MapComprehension expr2) {
      return expr1.Finite == expr2.Finite;
    }

    private static bool ShallowEq(SetComprehension expr1, SetComprehension expr2) {
      return expr1.TermIsImplicit == expr2.TermIsImplicit && //TODO
             expr1.Finite == expr2.Finite;
    }

    private static bool ShallowEq(ExistsExpr expr1, ExistsExpr expr2) {
      return true;
    }

    private static bool ShallowEq(ForallExpr expr1, ForallExpr expr2) {
      return true;
    }

    private static bool ShallowEq(QuantifierExpr expr1, QuantifierExpr expr2) { //FIXME are these TypeArgs still useful?
      if (expr1.TypeArgs.Count != expr2.TypeArgs.Count ||
          !SameNullity(expr1.Range, expr2.Range)) {
        return false;
      }

      if (expr1 is ExistsExpr && expr2 is ExistsExpr) {
        return ShallowEq((ExistsExpr)expr1, (ExistsExpr)expr2);
      } else if (expr1 is ForallExpr && expr2 is ForallExpr) {
        return ShallowEq((ForallExpr)expr1, (ForallExpr)expr2);
      } else {
        return false;
      }
    }

    private static bool ShallowEq(ComprehensionExpr expr1, ComprehensionExpr expr2) {
      if (!SameLists(expr1.BoundVars, expr2.BoundVars, SameBoundVar) ||
          !ShallowSameAttributes(expr1.Attributes, expr2.Attributes) ||
          // Filled in during resolution: !SameLists(expr1.Bounds, expr2.Bounds, ReferenceCompare) ||
          //                              !SameLists(expr1.MissingBounds, expr2.MissingBounds, SameBoundVar) ||
          !SameNullity(expr1.Range, expr2.Range)) { //TODO Check
        return false;
      }

      if (expr1 is LambdaExpr && expr2 is LambdaExpr) {
        return ShallowEq((LambdaExpr)expr1, (LambdaExpr)expr2);
      } else if (expr1 is MapComprehension && expr2 is MapComprehension) {
        return ShallowEq((MapComprehension)expr1, (MapComprehension)expr2);
      } else if (expr1 is SetComprehension && expr2 is SetComprehension) {
        return ShallowEq((SetComprehension)expr1, (SetComprehension)expr2);
      } else if (expr1 is QuantifierExpr && expr2 is QuantifierExpr) {
        return ShallowEq((QuantifierExpr)expr1, (QuantifierExpr)expr2);
      } else {
        return false; // ComprehensionExpr is abstract
      }
    }

    private static bool ShallowEq(NamedExpr expr1, NamedExpr expr2) {
      return expr1.Name == expr2.Name &&
             SameNullity(expr1.Contract, expr2.Contract);
    }

    private static bool ShallowEq(LetExpr expr1, LetExpr expr2) {
      return expr1.Exact == expr2.Exact &&
             ShallowSameAttributes(expr1.Attributes, expr2.Attributes);
    }

    private static bool ShallowEq(TernaryExpr expr1, TernaryExpr expr2) {
      return expr1.Op == expr2.Op;
    }

    private static bool ShallowEq(BinaryExpr expr1, BinaryExpr expr2) {
      Contract.Requires(expr1.ResolvedOp != BinaryExpr.ResolvedOpcode.YetUndetermined);
      Contract.Requires(expr2.ResolvedOp != BinaryExpr.ResolvedOpcode.YetUndetermined);
      return expr1.ResolvedOp == expr2.ResolvedOp;
    }

    private static bool ShallowEq(ConversionExpr expr1, ConversionExpr expr2) {
      return expr1.Type == expr2.Type; //TODO equality on types?
    }

    private static bool ShallowEq(UnaryOpExpr expr1, UnaryOpExpr expr2) {
      return expr1.Op == expr2.Op;
    }

    private static bool ShallowEq(UnaryExpr expr1, UnaryExpr expr2) {
      if (expr1 is ConversionExpr && expr2 is ConversionExpr) {
        return ShallowEq((ConversionExpr)expr1, (ConversionExpr)expr2);
      } else if (expr1 is UnaryOpExpr && expr2 is UnaryOpExpr) {
        return ShallowEq((UnaryOpExpr)expr1, (UnaryOpExpr)expr2);
      } else {
        return false; // UnaryExpr is abstract
      }
    }

    private static bool ShallowEq(MultiSetFormingExpr expr1, MultiSetFormingExpr expr2) {
      return true;
    }

    private static bool ShallowEq(OldExpr expr1, OldExpr expr2) {
      return true;
    }

    private static bool ShallowEq(FunctionCallExpr expr1, FunctionCallExpr expr2) {
      return expr1.Name == expr2.Name &&
             expr1.CoCall == expr2.CoCall && //TODO
             expr1.Function == expr2.Function; // TODO TypeArgumentSubstitutions?
    }

    private static bool ShallowEq(ApplyExpr expr1, ApplyExpr expr2) {
      return true;
    }

    private static bool ShallowEq(SeqUpdateExpr expr1, SeqUpdateExpr expr2) {
      Contract.Requires(expr1.ResolvedUpdateExpr != null && expr2.ResolvedUpdateExpr != null);
      return true;
    }

    private static bool ShallowEq(MultiSelectExpr expr1, MultiSelectExpr expr2) {
      return true;
    }

    private static bool ShallowEq(SeqSelectExpr expr1, SeqSelectExpr expr2) {
      return expr1.SelectOne == expr2.SelectOne &&
             SameNullity(expr1.Seq, expr2.Seq) &&
             SameNullity(expr1.E0, expr2.E0) &&
             SameNullity(expr1.E1, expr2.E1);
    }

    private static bool ShallowEq(MemberSelectExpr expr1, MemberSelectExpr expr2) {
      return expr1.MemberName == expr2.MemberName &&
             expr1.Member == expr2.Member &&
             SameLists(expr1.TypeApplication, expr2.TypeApplication, Type.Equals);
    }

    private static bool ShallowEq(SeqDisplayExpr expr1, SeqDisplayExpr expr2) {
      return true;
    }

    private static bool ShallowEq(MapDisplayExpr expr1, MapDisplayExpr expr2) {
      return expr1.Finite == expr2.Finite;
    }

    private static bool ShallowEq(MultiSetDisplayExpr expr1, MultiSetDisplayExpr expr2) {
      return true;
    }

    private static bool ShallowEq(SetDisplayExpr expr1, SetDisplayExpr expr2) {
      return expr1.Finite == expr2.Finite;
    }

    private static bool ShallowEq(DisplayExpression expr1, DisplayExpression expr2) {
      if (expr1 is SeqDisplayExpr && expr2 is SeqDisplayExpr) {
        return ShallowEq((SeqDisplayExpr)expr1, (SeqDisplayExpr)expr2);
      } else if (expr1 is MultiSetDisplayExpr && expr2 is MultiSetDisplayExpr) { //FIXME MultiSetDisplayExpr is not a DisplayExpression ??!
        return ShallowEq((MultiSetDisplayExpr)expr1, (MultiSetDisplayExpr)expr2);
      } else if (expr1 is SetDisplayExpr && expr2 is SetDisplayExpr) {
        return ShallowEq((SetDisplayExpr)expr1, (SetDisplayExpr)expr2);
      } else {
        return false;
      }
    }

    private static bool ShallowEq(AutoGhostIdentifierExpr expr1, AutoGhostIdentifierExpr expr2) {
      return true;
    }

    private static bool ShallowEq(IdentifierExpr expr1, IdentifierExpr expr2) {
      if (expr1.Name != expr2.Name ||
          expr1.Var != expr2.Var) {
            return false;
      }

      if (expr1 is AutoGhostIdentifierExpr && expr2 is AutoGhostIdentifierExpr) {
        return ShallowEq((AutoGhostIdentifierExpr)expr1, (AutoGhostIdentifierExpr)expr2);
      } else {
        return true;
      }
    }

    private static bool ShallowEq(ImplicitThisExpr expr1, ImplicitThisExpr expr2) {
      return true;
    }

    private static bool ShallowEq(ThisExpr expr1, ThisExpr expr2) {
      if (expr1 is ImplicitThisExpr && expr2 is ImplicitThisExpr) {
        return ShallowEq((ImplicitThisExpr)expr1, (ImplicitThisExpr)expr2);
      } else {
        return (expr1.GetType() == expr2.GetType()); // LiteralExpr is not abstract
      }
    }

    private static bool ShallowEq(DatatypeValue expr1, DatatypeValue expr2) {
      return // Implied by Ctor equality: expr1.DatatypeName == expr2.DatatypeName &&
             // Implied by Ctor equality: expr1.MemberName == expr2.MemberName &&
             expr1.Ctor == expr2.Ctor &&
             // Contextual information: expr1.IsCoCall == expr2.IsCoCall &&
             SameLists(expr1.InferredTypeArgs, expr2.InferredTypeArgs, Type.Equals);
    }

    private static bool ShallowEq(StringLiteralExpr expr1, StringLiteralExpr expr2) {
      return true;
    }

    private static bool ShallowEq(CharLiteralExpr expr1, CharLiteralExpr expr2) {
      return true;
    }

    private static bool ShallowEq(StaticReceiverExpr expr1, StaticReceiverExpr expr2) {
      return true;
    }

    private static bool ShallowEq(LiteralExpr expr1, LiteralExpr expr2) {
      if (expr1.Value != expr2.Value) {
        return false;
      }

      if (expr1 is StringLiteralExpr && expr2 is StringLiteralExpr) {
        return ShallowEq((StringLiteralExpr)expr1, (StringLiteralExpr)expr2);
      } else if (expr1 is CharLiteralExpr && expr2 is CharLiteralExpr) {
        return ShallowEq((CharLiteralExpr)expr1, (CharLiteralExpr)expr2);
      } else if (expr1 is StaticReceiverExpr && expr2 is StaticReceiverExpr) {
        return ShallowEq((StaticReceiverExpr)expr1, (StaticReceiverExpr)expr2);
      } else {
        return (expr1.GetType() == expr2.GetType()); // LiteralExpr is not abstract
      }
    }
  }
}
