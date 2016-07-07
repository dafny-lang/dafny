using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Triggers {
  internal class QuantifierCollector : TopDownVisitor<bool> {
    readonly ErrorReporter reporter;
    private readonly HashSet<Expression> quantifiers = new HashSet<Expression>();
    internal readonly HashSet<Expression> exprsInOldContext = new HashSet<Expression>();
    internal readonly List<QuantifiersCollection> quantifierCollections = new List<QuantifiersCollection>();

    public QuantifierCollector(ErrorReporter reporter) {
      Contract.Requires(reporter != null);
      this.reporter = reporter;
    }

    protected override bool VisitOneExpr(Expression expr, ref bool inOldContext) {
      var e = expr as ComprehensionExpr;

      // only consider quantifiers that are not empty (Bound.Vars.Count > 0)
      if (e != null && (e.BoundVars.Count > 0) && !quantifiers.Contains(e)) {
        if (e is SetComprehension || e is MapComprehension) {
          quantifiers.Add(e);
          quantifierCollections.Add(new QuantifiersCollection(e, Enumerable.Repeat(e, 1), reporter));
        } else if (e is ForallExpr || e is ExistsExpr) {
          var quantifier = e as QuantifierExpr;
          quantifiers.Add(quantifier);
          if (quantifier.SplitQuantifier != null) {
            var collection = quantifier.SplitQuantifier.Select(q => q as ComprehensionExpr).Where(q => q != null);
            quantifierCollections.Add(new QuantifiersCollection(e, collection, reporter));
            quantifiers.UnionWith(quantifier.SplitQuantifier);
          } else {
            quantifierCollections.Add(new QuantifiersCollection(e, Enumerable.Repeat(quantifier, 1), reporter));
          }
        }
      }

      if (expr is OldExpr) {
        inOldContext = true;
      } else if (inOldContext) { // FIXME be more restrctive on the type of stuff that we annotate
        exprsInOldContext.Add(expr);
      }

      return true;
    }

    protected override bool VisitOneStmt(Statement stmt, ref bool st) {
      if (stmt is ForallStmt) {
        ForallStmt s = (ForallStmt)stmt;
        if (s.ForallExpressions != null) {
          foreach (Expression expr in s.ForallExpressions) {
            VisitOneExpr(expr, ref st);
          }
        }
      }
      return true;
    }
  }
}
