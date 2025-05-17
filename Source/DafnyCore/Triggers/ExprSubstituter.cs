using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class ExprSubstituter : Substituter {
    private readonly List<Tuple<Expression, IdentifierExpr>> exprSubstMap;
    // In some places, substitutions are made in contexts that are not always evaluated. In particular,
    // this happens in short-circuit expressions (&&, ||, ==>, <==, if-then-else, and match). In those contexts,
    // "guardExpressions" keeps track of the conditions under which the currently visited expression is
    // evaluated.
    [CanBeNull] private AntecedentState antecedentState = null; // non-null if the traversal is inside a quantifier 

    public ExprSubstituter(List<Tuple<Expression, IdentifierExpr>> exprSubstMap)
      : base(null, new Dictionary<IVariable, Expression>(), new Dictionary<TypeParameter, Type>()) {
      this.exprSubstMap = exprSubstMap;
    }

    private bool TryGetExprSubst(Expression expr, out IdentifierExpr ie) {
      var entry = exprSubstMap.Find(x => Triggers.ExprExtensions.ExpressionEq(expr, x.Item1));
      if (entry != null) {
        // We have encountered a substitution, which we only expect to happen inside the quantifier, so these fields should be non-null
        Contract.Assert(antecedentState != null);
        antecedentState.AddGuard(entry.Item2, entry.Item2);

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
        // initialize the fields used to gather information about the traversal inside the quantifier
        var previousAntecedentState = antecedentState;
        antecedentState = new AntecedentState(expr.Origin);

        // Note: don't perform this substitution in .Attributes or .Bounds
        var newRange = e.Range == null ? null : Substitute(e.Range);
        if (newRange != null) {
          antecedentState.Push(newRange);
        }
        var newTerm = Substitute(e.Term);

        if (newRange == e.Range && newTerm == e.Term) {
          antecedentState = previousAntecedentState;
          return e;
        }

        var antecedent = antecedentState.CollectAntecedent(e.Origin, out var additionalBoundVars, out var additionalBoundedPools);
        var newBoundVars = new List<BoundVar>(e.BoundVars);
        newBoundVars.AddRange(additionalBoundVars!);
        var newBounds = new List<BoundedPool>();
        if (e.Bounds != null) {
          newBounds.AddRange(e.Bounds);
        }
        newBounds.AddRange(additionalBoundedPools!);
        newRange = newRange == null ? antecedent : Expression.CreateAnd(antecedent, newRange);

        QuantifierExpr newExpr;
        if (expr is ForallExpr) {
          newExpr = new ForallExpr(e.Origin, newBoundVars, newRange, newTerm, e.Attributes) { Bounds = newBounds };
        } else {
          Contract.Assert(expr is ExistsExpr);
          newExpr = new ExistsExpr(e.Origin, newBoundVars, newRange, newTerm, e.Attributes) { Bounds = newBounds };
        }
        newExpr.Type = expr.Type;

        antecedentState = previousAntecedentState;
        return newExpr;
      } else if (expr is BinaryExpr {
        ResolvedOp: BinaryExpr.ResolvedOpcode.And or BinaryExpr.ResolvedOpcode.Or or BinaryExpr.ResolvedOpcode.Imp
      } binaryExpr) {
        Contract.Assert(antecedentState != null);
        var e0 = Substitute(binaryExpr.E0);
        antecedentState.Push(e0);
        var e1 = Substitute(binaryExpr.E1);
        antecedentState.Pop();

        if (e0 != binaryExpr.E0 || e1 != binaryExpr.E1) {
          expr = new BinaryExpr(expr.Origin, binaryExpr.ResolvedOp, e0, e1) { Type = binaryExpr.Type };
        }
        return expr;
      } else if (expr is ITEExpr iteExpr) {
        Contract.Assert(antecedentState != null);
        var test = Substitute(iteExpr.Test);
        antecedentState.Push(test);
        var thn = Substitute(iteExpr.Thn);
        antecedentState.Pop();
        antecedentState.Push(Expression.CreateNot(test.Origin, test));
        var els = Substitute(iteExpr.Els);
        antecedentState.Pop();

        if (test != iteExpr.Test || thn != iteExpr.Thn || els != iteExpr.Els) {
          expr = new ITEExpr(expr.Origin, iteExpr.IsBindingGuard, test, thn, els) { Type = iteExpr.Type };
        }
        return expr;
      } else if (expr is MatchExpr or NestedMatchExpr) {
        var newExpr = base.Substitute(expr);
        Contract.Assert(newExpr == expr); // trigger-generation does not offer to rewrite things inside `match` expressions
        return newExpr;
      }
      return base.Substitute(expr);
    }

    private class AntecedentState(IOrigin origin) {
      private readonly Stack<Expression> guardExpressions = [];
      private readonly List<AntecedentTobeAdded> antecedentsToBeAdded = [];

      private record AntecedentTobeAdded(Expression Guard, IdentifierExpr Var, Expression Value);

      public void Push(Expression expr) {
        guardExpressions.Push(expr);
      }

      public void Pop() {
        guardExpressions.Pop();
      }

      public void AddGuard(IdentifierExpr idExpr, Expression rhs) {
        var context = guardExpressions!.Aggregate((Expression)Expression.CreateBoolLiteral(origin, true),
          (acc, e) => Expression.CreateAnd(acc, e)); // TODO: or should this be "e, acc"?
        var eq = new BinaryExpr(origin, BinaryExpr.ResolvedOpcode.EqCommon, idExpr, rhs) { Type = Type.Bool };
        var guard = Expression.CreateImplies(context, eq);
        antecedentsToBeAdded.Add(new AntecedentTobeAdded(guard, idExpr, rhs));
      }

      public Expression CollectAntecedent(IOrigin origin, out List<BoundVar> additionalBoundVars, out List<BoundedPool> additionalBoundedPools) {
        Contract.Assert(antecedentsToBeAdded != null);
        Expression result = Expression.CreateBoolLiteral(origin, true);
        additionalBoundVars = [];
        additionalBoundedPools = [];

        // For each variable in "antecedentsToBeAdded", construct the disjunction of its guards
        var variables = new HashSet<IdentifierExpr>(antecedentsToBeAdded.Select(a => a.Var));
        foreach (var v in variables) {
          additionalBoundVars.Add((BoundVar)v.Var);
#if PREVIOUS
        additionalBoundedPools.Add(new ExactBoundedPool(entry.Item1)); // TODO: this is not right if there's a further antecedent
#else
          additionalBoundedPools.Add(null);
#endif

          Expression value = null;
          Expression guard = Expression.CreateBoolLiteral(origin, false);
          foreach (var antecedentsForV in antecedentsToBeAdded.Where(a => a.Var == v)) {
            if (value == null) {
              value = antecedentsForV.Value;
            } else {
              // we expect the .Value to be the same for every record for this variable
              Contract.Assert(value == antecedentsForV.Value);
            }
            guard = Expression.CreateOr(guard, antecedentsForV.Guard);
          }
          result = Expression.CreateAnd(result, guard);
        }

        return result;
      }
    }
  }
}