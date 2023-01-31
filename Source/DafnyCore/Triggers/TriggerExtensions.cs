// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#define THROW_UNSUPPORTED_COMPARISONS

using Microsoft.Dafny;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny.Triggers {
  internal static class DeduplicateExtension {
    public static List<T> Deduplicate<T>(this IEnumerable<T> seq, Func<T, T, bool> eq) {
      List<T> deduplicated = new List<T>();

      foreach (var elem in seq) {
        if (!deduplicated.Any(other => eq(elem, other))) {
          deduplicated.Add(elem);
        }
      }

      return deduplicated;
    }
  }

  internal struct TriggerMatch {
    internal Expression Expr;
    internal Expression OriginalExpr;
    internal Dictionary<IVariable, Expression> Bindings;

    internal static bool Eq(TriggerMatch t1, TriggerMatch t2) {
      return ExprExtensions.ExpressionEq(t1.Expr, t2.Expr);
    }

    /// <summary>
    ///  This method checks whether this match could actually cause a loop, given a set of terms participating in a trigger;
    ///  to compute an answer, we match the Expr of this match against the Exprs of each of these term, allowing for harmless
    ///  variations. If any of these tests does match, this term likely won't cause a loop.
    ///  The boundVars list is useful to determine that forall x :: P(x) == P(y+z) does not loop.
    /// </summary>
    internal bool CouldCauseLoops(List<TriggerTerm> terms, ISet<BoundVar> boundVars) {
      var expr = Expr;
      return !terms.Any(term => term.Expr.ExpressionEqModuloExpressionsNotInvolvingBoundVariables(expr, boundVars));
    }
  }

  internal static class ExprExtensions {
    internal static bool IsInlineable(this LetExpr expr) {
      return expr.LHSs.All(p => p.Var != null) && expr.Exact;
    }

    internal static IEnumerable<Expression> AllSubExpressions(this Expression expr, bool wrapOld, bool strict, bool inlineLets = false) {
      var isOld = expr is OldExpr ? new HashSet<OldExpr>() { expr as OldExpr } : null;

      if (inlineLets && expr is LetExpr && ((LetExpr)expr).IsInlineable()) {
        var le = (LetExpr)expr;
        foreach (var subexpr in AllSubExpressions(Translator.InlineLet(le), wrapOld, strict, inlineLets)) {
          yield return subexpr;
        }
        // If strict is false, then the recursive call will already yield a copy of (the inlined version) of expr,
        // so there's no need to yield expr itself below.
        yield break;
      }

      foreach (var subexpr in expr.SubExpressions) {
        foreach (var r_subexpr in AllSubExpressions(subexpr, wrapOld, false, inlineLets)) {
          foreach (var e in TriggerUtils.MaybeWrapInOld(r_subexpr, isOld)) {
            yield return e;
          }
        }
      }

      if (expr is StmtExpr) {
        foreach (var r_subexpr in AllSubExpressions(((StmtExpr)expr).S, wrapOld, false, inlineLets)) {
          foreach (var e in TriggerUtils.MaybeWrapInOld(r_subexpr, isOld)) {
            yield return e;
          }
        }
      }

      if (!strict) {
        yield return expr;
      }
    }

    internal static IEnumerable<Expression> AllSubExpressions(this Statement stmt, bool wrapOld, bool strict, bool inlineLets = false) {
      foreach (var subexpr in stmt.SubExpressions) {
        foreach (var r_subexpr in AllSubExpressions(subexpr, wrapOld, false, inlineLets)) {
          yield return r_subexpr;
        }
      }

      foreach (var substmt in stmt.SubStatements) {
        foreach (var r_subexpr in AllSubExpressions(substmt, wrapOld, false, inlineLets)) {
          yield return r_subexpr;
        }
      }
    }

    internal static bool ExpressionEq(this Expression expr1, Expression expr2) {
      expr1 = expr1.Resolved;
      expr2 = expr2.Resolved;

      return ShallowEq_Top(expr1, expr2) && TriggerUtils.SameLists(expr1.SubExpressions, expr2.SubExpressions, (e1, e2) => ExpressionEq(e1, e2));
    }

    internal static bool ExpressionEqModuloExpressionsNotInvolvingBoundVariables(this Expression expr1, Expression expr2, ISet<BoundVar> boundVars) {
      expr1 = expr1.Resolved;
      expr2 = expr2.Resolved;

      if (expr1 is IdentifierExpr) {
        if (expr2 is IdentifierExpr) {
          return true;
        } else {
          var freeInE2 = FreeVariablesUtil.ComputeFreeVariables(expr2);
          freeInE2.IntersectWith(boundVars);
          return !freeInE2.Any();
        }
      }

      return ShallowEq_Top(expr1, expr2) && TriggerUtils.SameLists(expr1.SubExpressions,
        expr2.SubExpressions, (e1, e2) => ExpressionEqModuloExpressionsNotInvolvingBoundVariables(e1, e2, boundVars));
    }

    internal static bool MatchesTrigger(this Expression expr, Expression trigger, ISet<BoundVar> holes, Dictionary<IVariable, Expression> bindings) {
      expr = expr.Resolved;
      trigger = trigger.Resolved;

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

      return ShallowEq_Top(expr, trigger) && TriggerUtils.SameLists(expr.SubExpressions, trigger.SubExpressions, (e1, e2) => MatchesTrigger(e1, e2, holes, bindings));
    }

    private static TriggerMatch? MatchAgainst(this Expression expr, Expression trigger, IEnumerable<BoundVar> holes, Expression originalExpr) {
      var bindings = new Dictionary<IVariable, Expression>();
      if (expr.MatchesTrigger(trigger, new HashSet<BoundVar>(holes), bindings)) {
        return new TriggerMatch { Expr = expr, OriginalExpr = originalExpr ?? expr, Bindings = bindings };
      } else {
        return null;
      }
    }

    internal static IEnumerable<TriggerMatch> SubexpressionsMatchingTrigger(this ComprehensionExpr quantifier, Expression trigger) {
      return quantifier.AllSubExpressions(true, true, true)
        .Select(e => TriggerUtils.PrepareExprForInclusionInTrigger(e).MatchAgainst(trigger, quantifier.BoundVars, e))
        .Where(e => e.HasValue).Select(e => e.Value);
    }

    private static bool ShallowSameAttributes(Attributes attributes1, Attributes attributes2) {
      return TriggerUtils.SameLists(attributes1.AsEnumerable(), attributes2.AsEnumerable(), ShallowSameSingleAttribute);
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
              arg1.IsMutable == arg2.IsMutable &&
              ((arg1.Type == null && arg2.Type == null) || (arg1.Type != null && arg1.Type.Equals(arg2.Type))));
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
      } else if (expr1 is LetExpr && expr2 is LetExpr) {
        return ShallowEq((LetExpr)expr1, (LetExpr)expr2);
      } else if (expr1 is TernaryExpr && expr2 is TernaryExpr) {
        return ShallowEq((TernaryExpr)expr1, (TernaryExpr)expr2);
      } else if (expr1 is BinaryExpr && expr2 is BinaryExpr) {
        return ShallowEq((BinaryExpr)expr1, (BinaryExpr)expr2);
      } else if (expr1 is UnaryExpr && expr2 is UnaryExpr) {
        return ShallowEq((UnaryExpr)expr1, (UnaryExpr)expr2);
      } else if (expr1 is SeqConstructionExpr && expr2 is SeqConstructionExpr) {
        return ShallowEq((SeqConstructionExpr)expr1, (SeqConstructionExpr)expr2);
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
      } else if (expr1 is MapDisplayExpr && expr2 is MapDisplayExpr) { //Note: MapDisplayExpr is not a DisplayExpression
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
      return false;
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

    private static bool ShallowEq(QuantifierExpr expr1, QuantifierExpr expr2) {
      if (!TriggerUtils.SameNullity(expr1.SplitQuantifier, expr2.SplitQuantifier)) {
        return false;
      }

      if (expr1.SplitQuantifier != null && expr2.SplitQuantifier != null) {
        return ShallowEq_Top(expr1.SplitQuantifierExpression, expr2.SplitQuantifierExpression);
      }

      if (!TriggerUtils.SameNullity(expr1.Range, expr2.Range)) {
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
      if (!TriggerUtils.SameLists(expr1.BoundVars, expr2.BoundVars, SameBoundVar) ||
          !ShallowSameAttributes(expr1.Attributes, expr2.Attributes) ||
          // Filled in during resolution: !SameLists(expr1.Bounds, expr2.Bounds, ReferenceCompare) ||
          //                              !SameLists(expr1.MissingBounds, expr2.MissingBounds, SameBoundVar) ||
          !TriggerUtils.SameNullity(expr1.Range, expr2.Range)) { //TODO Check
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

    private static bool ShallowEq(LetExpr expr1, LetExpr expr2) {
      return expr1.Exact == expr2.Exact &&
             ShallowSameAttributes(expr1.Attributes, expr2.Attributes);
    }

    private static bool ShallowEq(TernaryExpr expr1, TernaryExpr expr2) {
      return expr1.Op == expr2.Op;
    }

    private static bool ShallowEq(BinaryExpr expr1, BinaryExpr expr2) {
      return expr1.ResolvedOp == expr2.ResolvedOp;
    }

    private static bool ShallowEq(ConversionExpr expr1, ConversionExpr expr2) {
      return Type.Equal_Improved(expr1.Type, expr2.Type);
    }

    private static bool ShallowEq(TypeTestExpr expr1, TypeTestExpr expr2) {
      return Type.Equal_Improved(expr1.Type, expr2.Type);
    }

    private static bool ShallowEq(UnaryOpExpr expr1, UnaryOpExpr expr2) {
      return expr1.ResolvedOp == expr2.ResolvedOp;
    }

    private static bool ShallowEq(UnaryExpr expr1, UnaryExpr expr2) {
      if (expr1 is ConversionExpr && expr2 is ConversionExpr) {
        return ShallowEq((ConversionExpr)expr1, (ConversionExpr)expr2);
      } else if (expr1 is TypeTestExpr && expr2 is TypeTestExpr) {
        return ShallowEq((TypeTestExpr)expr1, (TypeTestExpr)expr2);
      } else if (expr1 is UnaryOpExpr && expr2 is UnaryOpExpr) {
        return ShallowEq((UnaryOpExpr)expr1, (UnaryOpExpr)expr2);
      } else {
        return false; // UnaryExpr is abstract
      }
    }

    private static bool ShallowEq(MultiSetFormingExpr expr1, MultiSetFormingExpr expr2) {
      return true;
    }

    private static bool ShallowEq(SeqConstructionExpr expr1, SeqConstructionExpr expr2) {
      return true;
    }

    private static bool ShallowEq(OldExpr expr1, OldExpr expr2) {
      return true;
    }

    private static bool ShallowEq(FunctionCallExpr expr1, FunctionCallExpr expr2) {
      return expr1.Name.Value == expr2.Name.Value &&
             expr1.CoCall == expr2.CoCall && //TODO
             expr1.Function == expr2.Function; // TODO TypeArgumentSubstitutions?
    }

    private static bool ShallowEq(ApplyExpr expr1, ApplyExpr expr2) {
      return true;
    }

    private static bool ShallowEq(SeqUpdateExpr expr1, SeqUpdateExpr expr2) {
      return true;
    }

    private static bool ShallowEq(MultiSelectExpr expr1, MultiSelectExpr expr2) {
      return true;
    }

    private static bool ShallowEq(SeqSelectExpr expr1, SeqSelectExpr expr2) {
      return expr1.SelectOne == expr2.SelectOne &&
             TriggerUtils.SameNullity(expr1.Seq, expr2.Seq) &&
             TriggerUtils.SameNullity(expr1.E0, expr2.E0) &&
             TriggerUtils.SameNullity(expr1.E1, expr2.E1);
    }

    private static bool ShallowEq(MemberSelectExpr expr1, MemberSelectExpr expr2) {
      return expr1.MemberName == expr2.MemberName &&
             expr1.Member == expr2.Member &&
             TriggerUtils.SameLists(expr1.TypeApplication_AtEnclosingClass, expr2.TypeApplication_AtEnclosingClass, TypeEq) &&
             TriggerUtils.SameLists(expr1.TypeApplication_JustMember, expr2.TypeApplication_JustMember, TypeEq);
    }

    internal static bool TypeEq(Type type1, Type type2) {
      return type1.Equals(type2);
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
      } else if (expr1 is MultiSetDisplayExpr && expr2 is MultiSetDisplayExpr) {
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
             TriggerUtils.SameLists(expr1.InferredTypeArgs, expr2.InferredTypeArgs, TypeEq);
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
      if (!TriggerUtils.SameNullity(expr1.Value, expr2.Value) || (expr1.Value != null && !expr1.Value.Equals(expr2.Value))) {
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
