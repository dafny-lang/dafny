// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny.Triggers {

  /// <summary>
  /// See section 2.3 of "Trigger Selection Strategies to Stabilize Program Verifiers" to learn
  /// why we split quantifiers
  /// </summary>
  class QuantifierSplitter : BottomUpVisitor {
    /// This cache was introduced because some statements (notably calc) return the same SubExpression multiple times.
    /// This ended up causing an inconsistent situation when the calc statement's subexpressions contained the same quantifier
    /// twice: on the first pass that quantifier got its SplitQuantifiers generated, and on the the second pass these
    /// split quantifiers got re-split, creating a situation where the direct children of a split quantifier were
    /// also split quantifiers.
    private readonly Dictionary<QuantifierExpr, List<Expression>> splits = new();

    private static BinaryExpr.Opcode FlipOpcode(BinaryExpr.Opcode opCode) {
      if (opCode == BinaryExpr.Opcode.And) {
        return BinaryExpr.Opcode.Or;
      } else if (opCode == BinaryExpr.Opcode.Or) {
        return BinaryExpr.Opcode.And;
      } else {
        throw new ArgumentException();
      }
    }

    // NOTE: If we wanted to split quantifiers as far as possible, it would be
    // enough to put the formulas in DNF (for foralls) or CNF (for exists).
    // Unfortunately, this would cause ill-behaved quantifiers to produce
    // exponentially many smaller quantifiers. Thus we only do one step of
    // distributing, which takes care of the usual precondition case:
    //   forall x :: P(x) ==> (Q(x) && R(x))

    private static UnaryOpExpr Not(Expression expr) {
      return new UnaryOpExpr(expr.Origin, UnaryOpExpr.Opcode.Not, expr) { Type = expr.Type };
    }

    private static IEnumerable<Expression> SplitExpr(Expression expr, BinaryExpr.Opcode separator) {
      expr = expr.Resolved;
      var binary = expr as BinaryExpr;

      if (expr is UnaryOpExpr unary && unary.Op == UnaryOpExpr.Opcode.Not) {
        foreach (var e in SplitExpr(unary.E, FlipOpcode(separator))) { yield return Not(e); }
      } else if (binary != null && binary.Op == separator) {
        if (Expression.IsBoolLiteral(binary.E0, out var b) && (binary.Op == BinaryExpr.Opcode.And ? b : !b)) {
          // skip this unit element
        } else {
          foreach (var e in SplitExpr(binary.E0, separator)) { yield return e; }
        }
        foreach (var e in SplitExpr(binary.E1, separator)) { yield return e; }
      } else if (binary != null && binary.Op == BinaryExpr.Opcode.Imp && separator == BinaryExpr.Opcode.Or) {
        foreach (var e in SplitExpr(Not(binary.E0), separator)) { yield return e; }
        foreach (var e in SplitExpr(binary.E1, separator)) { yield return e; }
      } else {
        yield return expr;
      }
    }

    internal static IEnumerable<Expression> SplitAndStitch(BinaryExpr pair, BinaryExpr.Opcode separator) {
      foreach (var e1 in SplitExpr(pair.E1, separator)) {
        // Notice the token. This makes triggers/splitting-picks-the-right-tokens.dfy possible
        var nestedToken = new NestedOrigin(pair.Origin, e1.Origin);
        yield return new BinaryExpr(nestedToken, pair.Op, pair.E0, e1) { ResolvedOp = pair.ResolvedOp, Type = pair.Type };
      }
    }

    private static IEnumerable<Expression> SplitQuantifier(ComprehensionExpr quantifier) {
      var body = quantifier.Term;
      var binary = body as BinaryExpr;

      if (quantifier is ForallExpr) {
        IReadOnlyList<Expression> stream;
        if (binary != null && (binary.Op == BinaryExpr.Opcode.Imp || binary.Op == BinaryExpr.Opcode.Or)) {
          stream = SplitAndStitch(binary, BinaryExpr.Opcode.And).ToList();
        } else {
          stream = SplitExpr(body, BinaryExpr.Opcode.And).ToList();
        }

        foreach (var e in stream) {
          yield return new ForallExpr(quantifier.Origin, quantifier.BoundVars, quantifier.Range, e, TriggerUtils.CopyAttributes(quantifier.Attributes)) { Type = quantifier.Type, Bounds = quantifier.Bounds };
        }
      } else if (quantifier is ExistsExpr) {
        IReadOnlyList<Expression> stream;
        if (binary != null && binary.Op == BinaryExpr.Opcode.And) {
          stream = SplitAndStitch(binary, BinaryExpr.Opcode.Or).ToList();
        } else {
          stream = SplitExpr(body, BinaryExpr.Opcode.Or).ToList();
        }
        foreach (var e in stream) {
          yield return new ExistsExpr(quantifier.Origin, quantifier.BoundVars, quantifier.Range, e, TriggerUtils.CopyAttributes(quantifier.Attributes)) { Type = quantifier.Type, Bounds = quantifier.Bounds };
        }
      } else {
        yield return quantifier;
      }
    }

    private static bool AllowsSplitting(ComprehensionExpr quantifier) {
      // allow split if attributes doesn't contains "split" or it is "split: true" and it is not an empty QuantifierExpr (boundvar.count>0)
      bool splitAttr = true;
      return (!Attributes.ContainsBool(quantifier.Attributes, "split", ref splitAttr) || splitAttr) && (quantifier.BoundVars.Count > 0);
    }

    protected override void VisitOneExpr(Expression expr) {
      if (expr is QuantifierExpr quantifier) {
        Contract.Assert(quantifier.SplitQuantifier == null);
        if (!splits.ContainsKey(quantifier) && AllowsSplitting(quantifier)) {
          splits[quantifier] = SplitQuantifier(quantifier).Select(e => {
            e.SetOrigin(new AutoGeneratedOrigin(e.Origin));
            return e;
          }).ToList();
        }
      }

      if (expr is ITEExpr { IsBindingGuard: true } iteExpr) {
        splits.Remove((ExistsExpr)iteExpr.Test);
      }
    }

    protected override void VisitOneStmt(Statement stmt) {
      if (stmt is ForallStmt) {
        ForallStmt s = (ForallStmt)stmt;
        if (s.EffectiveEnsuresClauses != null) {
          foreach (Expression expr in s.EffectiveEnsuresClauses) {
            VisitOneExpr(expr);
          }
        }
      }

      if (stmt is IfStmt ifStatement && ifStatement.IsBindingGuard) {
        splits.Remove((ExistsExpr)ifStatement.Guard);
      }
    }

    /// <summary>
    /// See comments above definition of splits for reason why this method exists
    /// </summary>
    internal void Commit() {
      foreach (var quantifier in splits.Keys) {
        quantifier.SplitQuantifier = splits[quantifier];
      }
    }
  }
}
