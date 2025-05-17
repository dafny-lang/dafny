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
        antecedentState.AddGuard(entry.Item2, entry.Item1);

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
      } else if (expr is MatchExpr matchExpr) {
        Contract.Assert(antecedentState != null);
        var src = Substitute(matchExpr.Source);
        bool anythingChanged = src != matchExpr.Source;
        var cases = new List<MatchCaseExpr>();
        foreach (var mc in matchExpr.Cases) {
          var newBoundVars = CreateBoundVarSubstitutions(mc.Arguments, false);
          var sourceHasThisVariant = Expression.CreateFieldSelect(expr.Origin, src, mc.Ctor.QueryField);
          antecedentState.Push(sourceHasThisVariant);
          var body = Substitute(mc.Body);
          antecedentState.Pop();
          // undo any changes to substMap (could be optimized to do this only if newBoundVars != mc.Arguments)
          foreach (var bv in mc.Arguments) {
            substMap.Remove(bv);
          }
          // Put things together
          if (newBoundVars != mc.Arguments || body != mc.Body) {
            anythingChanged = true;
          }
          var newCaseExpr = new MatchCaseExpr(mc.Origin, mc.Ctor, mc.FromBoundVar, newBoundVars, body, mc.Attributes);
          newCaseExpr.Ctor = mc.Ctor;  // resolve here
          cases.Add(newCaseExpr);
        }

        if (anythingChanged) {
          var newME = new MatchExpr(expr.Origin, src, cases, matchExpr.UsesOptionalBraces);
          newME.MissingCases.AddRange(matchExpr.MissingCases);
          expr = newME;
        }
        return expr;
      }
      return base.Substitute(expr);
    }

    private class AntecedentState {
      private readonly IOrigin origin;
      private readonly Stack<Expression> guardExpressions;
      private readonly List<AntecedentTobeAdded> antecedentsToBeAdded = [];

      public AntecedentState(IOrigin origin) {
        this.origin = origin;
        guardExpressions = new Stack<Expression>();
        guardExpressions.Push(Expression.CreateBoolLiteral(origin, true));
      }

      private record AntecedentTobeAdded(BoundVar Var, Expression Guard, Expression Rhs);

      public void Push(Expression expr) {
        var top = guardExpressions.Peek();
        guardExpressions.Push(Expression.CreateAnd(top, expr));
      }

      public void Pop() {
        guardExpressions.Pop();
      }

      public void AddGuard(IdentifierExpr idExpr, Expression rhs) {
        var guard = guardExpressions.Peek();
        var variable = (BoundVar)idExpr.Var;
        if (!antecedentsToBeAdded.Any(a => a.Var == variable && a.Guard == guard)) {
          antecedentsToBeAdded.Add(new AntecedentTobeAdded(variable, guard, rhs));
        }
      }

      public Expression CollectAntecedent(IOrigin origin, out List<BoundVar> additionalBoundVars, out List<BoundedPool> additionalBoundedPools) {
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

          Expression rhs = null;
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