// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Triggers {
  internal class QuantifierCollector : TopDownVisitor<OldExpr/*?*/> {
    readonly ErrorReporter reporter;
    private readonly HashSet<Expression> quantifiers = new HashSet<Expression>();
    internal readonly Dictionary<Expression, HashSet<OldExpr>> exprsInOldContext = new Dictionary<Expression, HashSet<OldExpr>>();
    internal readonly List<ComprehensionTriggerGenerator> quantifierCollections = new List<ComprehensionTriggerGenerator>();

    private readonly List<Action> ActionsOnSelectedTriggers = new();

    public QuantifierCollector(ErrorReporter reporter) {
      Contract.Requires(reporter != null);
      this.reporter = reporter;
    }

    public void ApplyPostActions() {
      foreach (var action in ActionsOnSelectedTriggers) {
        action();
      }
    }

    protected override bool VisitOneExpr(Expression expr, ref OldExpr/*?*/ enclosingOldContext) {
      if (expr is LetExpr { Exact: false } letExpr) {
        // create a corresponding exists quantifier
        Contract.Assert(letExpr.RHSs.Count == 1); // let-such-that expressions have exactly 1 RHS
        // Note, trigger selection adds some attributes. These will remain in the following exists expression. So, Boogie translation needs
        // to look at letExpr.SuchThatExists.Attributes (not letExpr.Attributes) to find them.
        var existsExpr = new ExistsExpr(letExpr.tok, letExpr.RangeToken, letExpr.BoundVars.ToList(), null, letExpr.RHSs[0], letExpr.Attributes);
        ActionsOnSelectedTriggers.Add(() => {
          letExpr.Attributes = existsExpr.Attributes;
        });
        expr = existsExpr;
      }

      // only consider quantifiers that are not empty (Bound.Vars.Count > 0)
      if (expr is ComprehensionExpr e && e.BoundVars.Count > 0 && !quantifiers.Contains(e)) {
        if (e is SetComprehension or MapComprehension) {
          quantifiers.Add(e);
          quantifierCollections.Add(new ComprehensionTriggerGenerator(e, Enumerable.Repeat(e, 1), reporter));
        } else if (e is QuantifierExpr quantifier) {
          quantifiers.Add(quantifier);
          if (quantifier.SplitQuantifier != null) {
            var collection = quantifier.SplitQuantifier.Select(q => q as ComprehensionExpr).Where(q => q != null);
            quantifierCollections.Add(new ComprehensionTriggerGenerator(e, collection, reporter));
            quantifiers.UnionWith(quantifier.SplitQuantifier);
          } else {
            quantifierCollections.Add(new ComprehensionTriggerGenerator(e, Enumerable.Repeat(quantifier, 1), reporter));
          }
        }
      }

      if (expr is OldExpr oldExpr) {
        enclosingOldContext = oldExpr;
      } else if (enclosingOldContext != null) { // FIXME be more restrictive on the type of stuff that we annotate
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
      if (stmt is ForallStmt { EffectiveEnsuresClauses: { } effectiveEnsuresClauses }) {
        foreach (var expr in effectiveEnsuresClauses) {
          VisitOneExpr(expr, ref st);
        }
      }
      return true;
    }
  }
}
