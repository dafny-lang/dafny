#nullable enable
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
    private AntecedentState? antecedentState = null; // non-null if the traversal is inside a quantifier

    public bool ErrorDetected { get; private set; } = false;

    public ExprSubstituter(List<Tuple<Expression, IdentifierExpr>> exprSubstMap)
      : base(null, new Dictionary<IVariable, Expression>(), new Dictionary<TypeParameter, Type>()) {
      this.exprSubstMap = exprSubstMap;
    }

    private bool TryGetExprSubst(Expression expr, out IdentifierExpr? ie) {
      var entry = exprSubstMap.Find(x => Triggers.ExprExtensions.ExpressionEq(expr, x.Item1));
      if (entry != null) {
        // We have encountered a substitution, which we only expect to happen inside the quantifier, so these fields should be non-null
        Contract.Assert(antecedentState != null);
        if (antecedentState.AddGuard(entry.Item2, entry.Item1)) {
          ie = entry.Item2;
          return true;
        } else {
          ErrorDetected = true;
        }
      }
      ie = null;
      return false;
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

        var antecedent = antecedentState.CollectAntecedent(out var additionalBoundVars, out var additionalBoundedPools);
        var newBoundVars = new List<BoundVar>(e.BoundVars);
        newBoundVars.AddRange(additionalBoundVars!);
        var newBounds = new List<BoundedPool?>();
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
      } else if (expr is BinaryExpr { ResolvedOp: var op } binaryExpr &&
                 op is BinaryExpr.ResolvedOpcode.And or BinaryExpr.ResolvedOpcode.Or or BinaryExpr.ResolvedOpcode.Imp) {
        Contract.Assert(antecedentState != null);
        var e0 = Substitute(binaryExpr.E0);
        antecedentState.Push(op == BinaryExpr.ResolvedOpcode.Or ? Expression.CreateNot(expr.Origin, e0) : e0);
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
      } else if (expr is NestedMatchExpr or MatchExpr) {
        Contract.Assert(antecedentState != null);
        // Substitution inside cases is not supported. But it's much easier not to support substitution inside
        // the source expression of the match, either.
        antecedentState.PushUnsupportedMarker();
        expr = base.Substitute(expr);
        antecedentState.Pop();
        return expr;
      }
      return base.Substitute(expr);
    }

    private class AntecedentState {
      private readonly IOrigin origin;
      // A "null" value in "guardExpressions" indicates that a substitution in this state is not
      // supported. The reason for introducing such "unsupported markers" is because of "match"
      // expressions. Substitutions inside match expressions could be supported, but it would require
      // a more complicated stack (so that one can introduce let bindings in the resulting guard
      // expressions). Since a quantifier with a "match" inside is rare, and such a quantifier that
      // also needs a rewrite inside the "match" is even more rare, it does not seem worth the
      // effort to implement. Rather, if the substitution needs such an expression, the Substitute
      // operation above) will be flagged as not supported.
      private readonly Stack<Expression?> guardExpressions;
      private readonly List<AntecedentTobeAdded> antecedentsToBeAdded = [];

      public AntecedentState(IOrigin origin) {
        this.origin = origin;
        guardExpressions = new Stack<Expression?>();
        guardExpressions.Push(Expression.CreateBoolLiteral(origin, true));
      }

      private record AntecedentTobeAdded(BoundVar Var, Expression Guard, Expression Rhs);

      public void Push(Expression expr) {
        var top = guardExpressions.Peek();
        if (top == null) {
          guardExpressions.Push(null);
        } else {
          guardExpressions.Push(Expression.CreateAnd(top, expr));
        }
      }

      public void PushUnsupportedMarker() {
        guardExpressions.Push(null);
      }

      public void Pop() {
        guardExpressions.Pop();
      }

      /// <summary>
      /// Returns true on success.
      /// </summary>
      public bool AddGuard(IdentifierExpr idExpr, Expression rhs) {
        var guard = guardExpressions.Peek();
        if (guard == null) {
          return false;
        }
        var variable = (BoundVar)idExpr.Var;
        if (!antecedentsToBeAdded.Any(a => a.Var == variable && a.Guard == guard)) {
          antecedentsToBeAdded.Add(new AntecedentTobeAdded(variable, guard, rhs));
        }
        return true;
      }

      public Expression CollectAntecedent(out List<BoundVar> additionalBoundVars, out List<BoundedPool?> additionalBoundedPools) {
        Contract.Assert(antecedentsToBeAdded != null);
        Expression result = Expression.CreateBoolLiteral(origin, true);
        additionalBoundVars = [];
        additionalBoundedPools = [];

        // For each variable in "antecedentsToBeAdded", construct the disjunction of its guards
        var variables = new HashSet<BoundVar>(antecedentsToBeAdded.Select(a => a.Var));
        foreach (var v in variables) {
          additionalBoundVars.Add(v);
          // It would be nice to use "new ExactBoundedPool(antecedentsForV.Rhs)" as the BoundedPool for this variable. However,
          // because of the context antecedent, it may not hold. So, we use just "null".
          additionalBoundedPools.Add(null);

          Expression? rhs = null;
          Expression guard = Expression.CreateBoolLiteral(origin, false);
          foreach (var antecedentsForV in antecedentsToBeAdded.Where(a => a.Var == v)) {
            if (rhs == null) {
              rhs = antecedentsForV.Rhs;
            } else {
              // we expect the .Value to be the same for every record for this variable
              Contract.Assert(rhs == antecedentsForV.Rhs);
            }
            guard = Expression.CreateOr(guard, antecedentsForV.Guard);
          }
          var idExpr = new IdentifierExpr(origin, v);
          var eq = new BinaryExpr(origin, BinaryExpr.ResolvedOpcode.EqCommon, idExpr, rhs) { Type = Type.Bool };
          result = Expression.CreateAnd(result, Expression.CreateImplies(guard, eq));
        }

        return result;
      }
    }
  }
}