using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  public class ExprSubstituter : Substituter {
    readonly List<Tuple<Expression, IdentifierExpr>> exprSubstMap;
    List<Tuple<Expression, IdentifierExpr>> usedSubstMap;

    public ExprSubstituter(List<Tuple<Expression, IdentifierExpr>> exprSubstMap)
      : base(null, new Dictionary<IVariable, Expression>(), new Dictionary<TypeParameter, Type>()) {
      this.exprSubstMap = exprSubstMap;
      this.usedSubstMap = new List<Tuple<Expression, IdentifierExpr>>();
    }

    public bool TryGetExprSubst(Expression expr, out IdentifierExpr ie) {
      var entry = usedSubstMap.Find(x => Triggers.ExprExtensions.ExpressionEq(expr, x.Item1));
      if (entry != null) {
        ie = entry.Item2;
        return true;
      }
      entry = exprSubstMap.Find(x => Triggers.ExprExtensions.ExpressionEq(expr, x.Item1));
      if (entry != null) {
        usedSubstMap.Add(entry);
        ie = entry.Item2;
        return true;
      } else {
        ie = null;
        return false;
      }
    }

    public override Expression Substitute(Expression expr) {
      if (TryGetExprSubst(expr, out var ie)) {
        Contract.Assert(ie != null);
        return ie;
      }
      if (expr is QuantifierExpr e) {
        var newAttrs = SubstAttributes(e.Attributes);
        var newRange = e.Range == null ? null : Substitute(e.Range);
        var newTerm = Substitute(e.Term);
        var newBounds = SubstituteBoundedPoolList(e.Bounds);
        if (newAttrs == e.Attributes && newRange == e.Range && newTerm == e.Term && newBounds == e.Bounds) {
          return e;
        }

        var newBoundVars = new List<BoundVar>(e.BoundVars);
        if (newBounds == null) {
          newBounds = new List<ComprehensionExpr.BoundedPool>();
        } else if (newBounds == e.Bounds) {
          // create a new list with the same elements, since the .Add operations below would otherwise add elements to the original e.Bounds
          newBounds = new List<ComprehensionExpr.BoundedPool>(newBounds);
        }

        // conjoin all the new equalities to the range of the quantifier
        foreach (var entry in usedSubstMap) {
          var eq = new BinaryExpr(e.RangeToken, BinaryExpr.ResolvedOpcode.EqCommon, entry.Item2, entry.Item1);
          newRange = newRange == null ? eq : new BinaryExpr(e.RangeToken, BinaryExpr.ResolvedOpcode.And, eq, newRange);
          newBoundVars.Add((BoundVar)entry.Item2.Var);
          newBounds.Add(new ComprehensionExpr.ExactBoundedPool(entry.Item1));
        }

        QuantifierExpr newExpr;
        if (expr is ForallExpr) {
          newExpr = new ForallExpr(e.RangeToken, newBoundVars, newRange, newTerm, newAttrs) { Bounds = newBounds, OverrideToken = expr.OverrideToken };
        } else {
          Contract.Assert(expr is ExistsExpr);
          newExpr = new ExistsExpr(e.RangeToken, newBoundVars, newRange, newTerm, newAttrs) { Bounds = newBounds, OverrideToken = expr.OverrideToken };
        }
        usedSubstMap.Clear();

        newExpr.Type = expr.Type;
        return newExpr;
      }
      return base.Substitute(expr);
    }
  }
}