using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny {
  public class ExprSubstituter : Substituter {
    private readonly List<Tuple<Expression, IdentifierExpr>> exprSubstMap;
    // The following 3 fields are non-null if the traversal is inside a quantifier
    [CanBeNull] private Expression antecedentToBeAdded = null;
    [CanBeNull] private List<BoundVar> additionalBoundVars = null;
    [CanBeNull] private List<BoundedPool> additionalBoundedPools = null;
    // In some places, substitutions are made in contexts that are not always evaluated. In particular,
    // this happens in short-circuit expressions (&&, ||, ==>, <==, if-then-else, and match). In those contexts,
    // "guardExpressions" keeps track of the conditions under which the currently visited expression is
    // evaluated.
    [CanBeNull] private Stack<Expression> guardExpressions = [];

    public ExprSubstituter(List<Tuple<Expression, IdentifierExpr>> exprSubstMap)
      : base(null, new Dictionary<IVariable, Expression>(), new Dictionary<TypeParameter, Type>()) {
      this.exprSubstMap = exprSubstMap;
    }

    private bool TryGetExprSubst(Expression expr, out IdentifierExpr ie) {
      var entry = exprSubstMap.Find(x => Triggers.ExprExtensions.ExpressionEq(expr, x.Item1));
      if (entry != null) {
        // We have encountered a substitution, which we only expect to happen inside the quantifier, so these fields should be non-null
        Contract.Assert(antecedentToBeAdded != null && additionalBoundVars != null && additionalBoundedPools != null);
        var context = guardExpressions.Aggregate((Expression)Expression.CreateBoolLiteral(expr.Origin, true),
          (acc, e) => Expression.CreateAnd(acc, e)); // TODO: or should this be "e, acc"?
        var eq = new BinaryExpr(expr.Origin, BinaryExpr.ResolvedOpcode.EqCommon, entry.Item2, entry.Item1) { Type = Type.Bool };
        var antecedent = Expression.CreateImplies(context, eq);
        antecedentToBeAdded = Expression.CreateAnd(antecedentToBeAdded, antecedent);
        additionalBoundVars.Add((BoundVar)entry.Item2.Var);
        additionalBoundedPools.Add(new ExactBoundedPool(entry.Item1)); // TODO: this is not right if there's a further antecedent

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
        var previousAntecedentToBeAdded = antecedentToBeAdded;
        var previousAdditionalBoundVars = additionalBoundVars;
        var previousAdditionalBoundedPools = additionalBoundedPools;
        var previousGuardExpressions = guardExpressions;
        antecedentToBeAdded = Expression.CreateBoolLiteral(e.Origin, true);
        additionalBoundVars = [];
        additionalBoundedPools = [];
        guardExpressions = new Stack<Expression>();

        // Note: don't perform this substitution in .Attributes or .Bounds
        var newRange = e.Range == null ? null : Substitute(e.Range);
        if (newRange != null) {
          guardExpressions.Push(newRange);
        }
        var newTerm = Substitute(e.Term);

        if (newRange == e.Range && newTerm == e.Term) {
          Contract.Assert(additionalBoundVars?.Count == 0);
          antecedentToBeAdded = previousAntecedentToBeAdded;
          additionalBoundVars = previousAdditionalBoundVars;
          additionalBoundedPools = previousAdditionalBoundedPools;
          guardExpressions = previousGuardExpressions;
          return e;
        }

        var newBoundVars = new List<BoundVar>(e.BoundVars);
        newBoundVars.AddRange(additionalBoundVars!);
        var newBounds = new List<BoundedPool>();
        if (e.Bounds != null) {
          newBounds.AddRange(e.Bounds);
        }
        newBounds.AddRange(additionalBoundedPools!);

        newRange = newRange == null ? antecedentToBeAdded : Expression.CreateAnd(antecedentToBeAdded, newRange);

        QuantifierExpr newExpr;
        if (expr is ForallExpr) {
          newExpr = new ForallExpr(e.Origin, newBoundVars, newRange, newTerm, e.Attributes) { Bounds = newBounds };
        } else {
          Contract.Assert(expr is ExistsExpr);
          newExpr = new ExistsExpr(e.Origin, newBoundVars, newRange, newTerm, e.Attributes) { Bounds = newBounds };
        }
        newExpr.Type = expr.Type;

        antecedentToBeAdded = previousAntecedentToBeAdded;
        additionalBoundVars = previousAdditionalBoundVars;
        additionalBoundedPools = previousAdditionalBoundedPools;
        guardExpressions = previousGuardExpressions;
        return newExpr;
      } else if (expr is BinaryExpr { Op: BinaryExpr.Opcode.And or BinaryExpr.Opcode.Or or BinaryExpr.Opcode.Imp or BinaryExpr.Opcode.Exp } binaryExpr) {
        Contract.Assert(guardExpressions != null);
        Expression e0, e1;
        if (binaryExpr.Op != BinaryExpr.Opcode.Exp) {
          e0 = Substitute(binaryExpr.E0);
          guardExpressions.Push(e0);
          e1 = Substitute(binaryExpr.E1);
          guardExpressions.Pop();
        } else {
          e1 = Substitute(binaryExpr.E1);
          guardExpressions.Push(e1);
          e0 = Substitute(binaryExpr.E0);
          guardExpressions.Pop();
        }

        if (e0 != binaryExpr.E0 || e1 != binaryExpr.E1) {
          expr = new BinaryExpr(expr.Origin, binaryExpr.Op, e0, e1) {
            ResolvedOp = binaryExpr.ResolvedOp,
            Type = binaryExpr.Type
          };
        }
        return expr;
      } else if (expr is ITEExpr iteExpr) {
        Contract.Assert(guardExpressions != null);
        var test = Substitute(iteExpr.Test);
        guardExpressions.Push(test);
        var thn = Substitute(iteExpr.Thn);
        guardExpressions.Pop();
        guardExpressions.Push(Expression.CreateNot(test.Origin, test));
        var els = Substitute(iteExpr.Els);
        guardExpressions.Pop();
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
  }
}