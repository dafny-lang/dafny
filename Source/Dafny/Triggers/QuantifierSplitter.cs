using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny.Triggers {
  class QuantifierSplitter : BottomUpVisitor {
    internal enum Quantifier { Forall, Exists }

    internal static IEnumerable<Expression> BreakQuantifier(Expression expr, Quantifier quantifier) {
      expr = expr.Resolved;
      var binary = expr as BinaryExpr;

      if (binary == null) {
        yield return expr;
        yield break;
      }

      var e0 = binary.E0;
      var e1 = binary.E1;

      if ((quantifier == Quantifier.Forall && binary.Op == BinaryExpr.Opcode.And) ||
          (quantifier == Quantifier.Exists && binary.Op == BinaryExpr.Opcode.Or)) {
        foreach (var e in BreakQuantifier(e0, quantifier)) { yield return e; }
        foreach (var e in BreakQuantifier(e1, quantifier)) { yield return e; }
      } else if (binary.Op == BinaryExpr.Opcode.Imp) {
        if (quantifier == Quantifier.Forall) {
          foreach (var e in BreakImplication(e0, e1, quantifier, expr.tok)) { yield return e; }
        } else {
          yield return new UnaryOpExpr(e1.tok, UnaryOpExpr.Opcode.Not, e1); // FIXME should be broken further
          foreach (var e in BreakQuantifier(e1, quantifier)) { yield return e; }
        }
      } else {
        yield return expr;
      }
    }

    internal static IEnumerable<Expression> BreakImplication(Expression ante, Expression post, Quantifier quantifier, IToken tok) { // FIXME: should work for exists and &&
      foreach (var small_post in BreakQuantifier(post, quantifier)) {
        var bin_post = small_post as BinaryExpr;
        if (bin_post == null || bin_post.Op != BinaryExpr.Opcode.Imp) {
          yield return new BinaryExpr(tok, BinaryExpr.Opcode.Imp, ante, small_post);
        } else { // bin_post is an implication
          var large_ante = new BinaryExpr(ante.tok, BinaryExpr.Opcode.And, ante, bin_post.E0);
          foreach (var imp in BreakImplication(large_ante, bin_post.E1, quantifier, tok)) {
            yield return imp;
          }
        }
      }
    }
    
    protected override void VisitOneExpr(Expression expr) { //FIXME: This doesn't save the rewritten quantifier
      var forall = expr as ForallExpr;
      var exists = expr as ExistsExpr;

      if (forall != null && TriggerUtils.NeedsAutoTriggers(forall)) {
        var rew = BreakQuantifier(forall.LogicalBody(), Quantifier.Forall);
        //Console.WriteLine("!!! {0} => {1}", Printer.ExprToString(expr), rew.MapConcat(Printer.ExprToString, " ||| "));
      } else if (exists != null && TriggerUtils.NeedsAutoTriggers(exists)) {
        var rew = BreakQuantifier(exists.LogicalBody(), Quantifier.Exists);
        //Console.WriteLine("!!! {0} => {1}", Printer.ExprToString(expr), rew.MapConcat(Printer.ExprToString, " ||| "));
      }
    }
  }
}
