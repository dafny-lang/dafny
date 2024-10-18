// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;

namespace Microsoft.Dafny.Triggers {
  internal class QuantifierCollector : TopDownVisitor<OldExpr/*?*/> {
    readonly ErrorReporter reporter;
    private readonly HashSet<Expression> quantifiers = new HashSet<Expression>();
    internal readonly Dictionary<Expression, HashSet<OldExpr>> exprsInOldContext = new Dictionary<Expression, HashSet<OldExpr>>();
    internal readonly List<ComprehensionTriggerGenerator> quantifierCollections = new List<ComprehensionTriggerGenerator>();

    public QuantifierCollector(ErrorReporter reporter) {
      Contract.Requires(reporter != null);
      this.reporter = reporter;
    }

    public void AddComprehension(ComprehensionExpr comprehensionExpr, [CanBeNull] List<Expression> splitQuantifier) {
      quantifiers.Add(comprehensionExpr);
      if (splitQuantifier != null) {
        var collection = splitQuantifier.OfType<ComprehensionExpr>();
        quantifierCollections.Add(new ComprehensionTriggerGenerator(comprehensionExpr, collection, reporter));
        quantifiers.UnionWith(splitQuantifier);
      } else {
        quantifierCollections.Add(new ComprehensionTriggerGenerator(comprehensionExpr, Enumerable.Repeat(comprehensionExpr, 1), reporter));
      }
    }

    protected override bool VisitOneExpr(Expression expr, ref OldExpr/*?*/ enclosingOldContext) {
      // only consider quantifiers that are not empty (Bound.Vars.Count > 0)
      if (expr is ComprehensionExpr e && e.BoundVars.Count > 0 && !quantifiers.Contains(e)) {
        if (e is SetComprehension or MapComprehension) {
          AddComprehension(e, null);
        } else if (e is QuantifierExpr quantifier) {
          AddComprehension(quantifier, quantifier.SplitQuantifier);
        }
      }

      if (expr is OldExpr oldExpr) {
        enclosingOldContext = oldExpr;
      } else if (enclosingOldContext != null) { // FIXME be more restrctive on the type of stuff that we annotate
        // Add the association (expr, oldContext) to exprsInOldContext. However, due to chaining expressions,
        // expr may already be a key in exprsInOldContext.
        if (exprsInOldContext.TryGetValue(expr, out var prevValue)) {
          prevValue.Add(enclosingOldContext);
        } else {
          var single = new HashSet<OldExpr>() { enclosingOldContext };
          exprsInOldContext.Add(expr, single);
        }
      }

      return true;
    }

    protected override bool VisitOneStmt(Statement stmt, ref OldExpr/*?*/ st) {
      if (stmt is ForallStmt) {
        ForallStmt s = (ForallStmt)stmt;
        if (s.EffectiveEnsuresClauses != null) {
          foreach (Expression expr in s.EffectiveEnsuresClauses) {
            VisitOneExpr(expr, ref st);
          }
        }
      }
      return true;
    }
  }
}
