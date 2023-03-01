// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny.Triggers {
  class QuantifierSplitter : BottomUpVisitor {
    /// This cache was introduced because some statements (notably calc) return the same SubExpression multiple times.
    /// This ended up causing an inconsistent situation when the calc statement's subexpressions contained the same quantifier
    /// twice: on the first pass that quantifier got its SplitQuantifiers generated, and on the the second pass these
    /// split quantifiers got re-split, creating a situation where the direct children of a split quantifier were
    /// also split quantifiers.
    private Dictionary<QuantifierExpr, List<Expression>> splits = new Dictionary<QuantifierExpr, List<Expression>>();

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
      return new UnaryOpExpr(expr.tok, UnaryOpExpr.Opcode.Not, expr) { Type = expr.Type };
    }

    internal static IEnumerable<Expression> SplitExpr(Expression expr, BinaryExpr.Opcode separator) {
      expr = expr.Resolved;
      var unary = expr as UnaryOpExpr;
      var binary = expr as BinaryExpr;

      if (unary != null && unary.Op == UnaryOpExpr.Opcode.Not) {
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
        var nestedToken = new NestedToken(pair.tok, e1.tok);
        yield return new BinaryExpr(nestedToken, pair.Op, pair.E0, e1) { ResolvedOp = pair.ResolvedOp, Type = pair.Type };
      }
    }

    internal static IEnumerable<Expression> SplitQuantifier(ComprehensionExpr quantifier) {
      var body = quantifier.Term;
      var binary = body as BinaryExpr;

      if (quantifier is ForallExpr) {
        IEnumerable<Expression> stream;
        if (binary != null && (binary.Op == BinaryExpr.Opcode.Imp || binary.Op == BinaryExpr.Opcode.Or)) {
          stream = SplitAndStitch(binary, BinaryExpr.Opcode.And);
        } else {
          stream = SplitExpr(body, BinaryExpr.Opcode.And);
        }
        foreach (var e in stream) {
          var tok = new NestedToken(quantifier.tok, e.tok, "in subexpression at");
          yield return new ForallExpr(tok, quantifier.RangeToken, quantifier.BoundVars, quantifier.Range, e, TriggerUtils.CopyAttributes(quantifier.Attributes)) { Type = quantifier.Type, Bounds = quantifier.Bounds };
        }
      } else if (quantifier is ExistsExpr) {
        IEnumerable<Expression> stream;
        if (binary != null && binary.Op == BinaryExpr.Opcode.And) {
          stream = SplitAndStitch(binary, BinaryExpr.Opcode.Or);
        } else {
          stream = SplitExpr(body, BinaryExpr.Opcode.Or);
        }
        foreach (var e in stream) {
          var tok = body?.tok == e.tok ? quantifier.tok : new NestedToken(quantifier.tok, e.tok, "in subexpression at");
          yield return new ExistsExpr(tok, quantifier.RangeToken, quantifier.BoundVars, quantifier.Range, e, TriggerUtils.CopyAttributes(quantifier.Attributes)) { Type = quantifier.Type, Bounds = quantifier.Bounds };
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
      var quantifier = expr as QuantifierExpr;
      if (quantifier != null) {
        Contract.Assert(quantifier.SplitQuantifier == null);
        if (!splits.ContainsKey(quantifier) && AllowsSplitting(quantifier)) {
          splits[quantifier] = SplitQuantifier(quantifier).ToList();
        }
      }

      if (expr is ITEExpr iteExpr && iteExpr.IsBindingGuard) {
        splits.Remove((ExistsExpr)iteExpr.Test);
      }
    }

    protected override void VisitOneStmt(Statement stmt) {
      if (stmt is ForallStmt) {
        ForallStmt s = (ForallStmt)stmt;
        if (s.ForallExpressions != null) {
          foreach (Expression expr in s.ForallExpressions) {
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

  class MatchingLoopRewriter {
    public MatchingLoopRewriter(DafnyOptions options)
    {
      triggersCollector = new TriggersCollector(new Dictionary<Expression, HashSet<OldExpr>>(), options);
    }

    TriggersCollector triggersCollector;
    List<Tuple<Expression, IdentifierExpr>> substMap;

    public QuantifierExpr RewriteMatchingLoops(QuantifierWithTriggers q) {
      // rewrite quantifier to avoid matching loops
      // before:
      //    assert forall i :: 0 <= i < a.Length-1 ==> a[i] <= a[i+1];
      // after:
      //    assert forall i,j :: j == i+1 ==> 0 <= i < a.Length-1 ==> a[i] <= a[j];
      substMap = new List<Tuple<Expression, IdentifierExpr>>();
      foreach (var m in q.LoopingMatches) {
        var e = m.OriginalExpr;
        if (TriggersCollector.IsPotentialTriggerCandidate(e) && triggersCollector.IsTriggerKiller(e)) {
          foreach (var sub in e.SubExpressions) {
            if (triggersCollector.IsTriggerKiller(sub) && (!TriggersCollector.IsPotentialTriggerCandidate(sub))) {
              var entry = substMap.Find(x => ExprExtensions.ExpressionEq(sub, x.Item1));
              if (entry == null) {
                var newBv = new BoundVar(sub.tok, "_t#" + substMap.Count, sub.Type);
                var ie = new IdentifierExpr(sub.tok, newBv.Name);
                ie.Var = newBv;
                ie.Type = newBv.Type;
                substMap.Add(new Tuple<Expression, IdentifierExpr>(sub, ie));
              }
            }
          }
        }
      }

      var expr = (QuantifierExpr)q.quantifier;
      if (substMap.Count > 0) {
        var s = new ExprSubstituter(substMap);
        expr = s.Substitute(q.quantifier) as QuantifierExpr;
      } else {
        // make a copy of the expr
        if (expr is ForallExpr) {
          expr = new ForallExpr(expr.tok, expr.RangeToken, expr.BoundVars, expr.Range, expr.Term, TriggerUtils.CopyAttributes(expr.Attributes)) { Type = expr.Type, Bounds = expr.Bounds };
        } else {
          expr = new ExistsExpr(expr.tok, expr.RangeToken, expr.BoundVars, expr.Range, expr.Term, TriggerUtils.CopyAttributes(expr.Attributes)) { Type = expr.Type, Bounds = expr.Bounds };
        }
      }
      return expr;
    }
  }
}
