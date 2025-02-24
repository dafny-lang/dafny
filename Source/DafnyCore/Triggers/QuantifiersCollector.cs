// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Action = System.Action;
using JetBrains.Annotations;

namespace Microsoft.Dafny.Triggers {
  internal class QuantifierCollector : TopDownVisitor<OldExpr/*?*/> {
    readonly ErrorReporter reporter;
    private readonly HashSet<Expression> quantifiers = [];
    internal readonly Dictionary<Expression, HashSet<OldExpr>> exprsInOldContext = new Dictionary<Expression, HashSet<OldExpr>>();
    internal readonly List<ComprehensionTriggerGenerator> quantifierCollections = [];

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
      if (expr is LetExpr { Exact: false } letExpr) {
        // create a corresponding exists quantifier
        Contract.Assert(letExpr.RHSs.Count == 1); // let-such-that expressions have exactly 1 RHS
        // Note, trigger selection adds some attributes. These will remain in the following exists expression. They
        // make it back to the letExpr via the ActionsOnSelectedTriggers below.
        var existsExpr = new ExistsExpr(letExpr.Origin, letExpr.BoundVars.ToList(), null, letExpr.RHSs[0],
          new Attributes("_delayTriggerWarning", new List<Expression>(), letExpr.Attributes)) {
          Type = Type.Bool
        };

        ActionsOnSelectedTriggers.Add(() => {
          letExpr.Attributes = existsExpr.Attributes;
        });
        expr = existsExpr;
      }

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
      } else if (stmt is AssignSuchThatStmt { AssumeToken: null } assignSuchThatStmt) {
        // Create a corresponding exists quantifier. Annoyingly, an ExistsExpr uses BoundVar's whereas the variables
        // in the AssignSuchThatStmt are IVariable's, so we have to do a substitution back and forth.
        var substLocalToBoundVar = new Dictionary<IVariable, Expression>();
        var substBoundVarToLocal = new Dictionary<IVariable, Expression>();
        var boundVars = new List<BoundVar>();
        foreach (var localIdentifierExpr in assignSuchThatStmt.GetAssignedLocals()) {
          var local = localIdentifierExpr.Var;
          var boundVar = new BoundVar(local.Origin, local.Name, local.Type);
          var boundVarIdentifierExpr = new IdentifierExpr(boundVar.Origin, boundVar);
          boundVars.Add(boundVar);
          substLocalToBoundVar.Add(local, boundVarIdentifierExpr);
          substBoundVarToLocal.Add(boundVar, localIdentifierExpr);
        }

        var substituterTo = new Substituter(null, substLocalToBoundVar, new Dictionary<TypeParameter, Type>());
        var existsExpr = new ExistsExpr(assignSuchThatStmt.Origin, boundVars, null,
          substituterTo.Substitute(assignSuchThatStmt.Expr),
          new Attributes("_delayTriggerWarning", new List<Expression>(), substituterTo.SubstAttributes(assignSuchThatStmt.Attributes))) {
          Type = Type.Bool
        };

        ActionsOnSelectedTriggers.Add(() => {
          var substituteFrom = new Substituter(null, substBoundVarToLocal, new Dictionary<TypeParameter, Type>());
          var updatedAttributes = substituteFrom.SubstAttributes(existsExpr.Attributes);
          assignSuchThatStmt.Attributes = updatedAttributes;
        });

        VisitOneExpr(existsExpr, ref st);
      }

      return true;
    }
  }
}
