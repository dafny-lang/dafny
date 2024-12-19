//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny {
  public partial class BoogieGenerator {
    public const string DefassPrefix = "defass#";

    #region Definite-assignment tracking

    bool NeedsDefiniteAssignmentTracker(bool isGhost, Type type, bool isField) {
      Contract.Requires(type != null);

      if (options.DefiniteAssignmentLevel == 0) {
        return false;
      } else if (options.DefiniteAssignmentLevel == 1 ||
                 (options.DefiniteAssignmentLevel == 4 && isField && !options.ForbidNondeterminism)) {
        if (isGhost && type.IsNonempty) {
          return false;
        } else if (!isGhost && type.HasCompilableValue) {
          return false;
        }
      }

      return true;
    }

    Bpl.Expr /*?*/ AddDefiniteAssignmentTracker(IVariable p, Variables localVariables, bool isOutParam = false,
      bool forceGhostVar = false) {
      Contract.Requires(p != null);
      Contract.Requires(localVariables != null);

      if (!NeedsDefiniteAssignmentTracker(p.IsGhost || forceGhostVar, p.Type, false)) {
        return null;
      }

      Bpl.Variable tracker;
      if (isOutParam) {
        tracker = new Bpl.Formal(p.Tok, new Bpl.TypedIdent(p.Tok, DefassPrefix + p.UniqueName, Bpl.Type.Bool), false);
      } else {
        tracker = new Bpl.LocalVariable(p.Tok, new Bpl.TypedIdent(p.Tok, DefassPrefix + p.UniqueName, Bpl.Type.Bool));
      }

      tracker = localVariables.GetOrAdd(tracker);
      var ie = new Bpl.IdentifierExpr(p.Tok, tracker);
      DefiniteAssignmentTrackers = DefiniteAssignmentTrackers.Add(p.UniqueName, ie);
      return ie;
    }

    void AddExistingDefiniteAssignmentTracker(IVariable p, bool forceGhostVar) {
      Contract.Requires(p != null);

      if (DefiniteAssignmentTrackers.ContainsKey(p.UniqueName)) {
        return;
      }

      if (!NeedsDefiniteAssignmentTracker(p.IsGhost || forceGhostVar, p.Type, false)) {
        return;
      }

      var ie = new Bpl.IdentifierExpr(p.Tok, DefassPrefix + p.UniqueName, Bpl.Type.Bool);
      DefiniteAssignmentTrackers = DefiniteAssignmentTrackers.Add(p.UniqueName, ie);
    }

    void AddDefiniteAssignmentTrackerSurrogate(Field field, TopLevelDeclWithMembers enclosingClass,
      Variables localVariables, bool forceGhostVar) {
      Contract.Requires(field != null);
      Contract.Requires(localVariables != null);

      var type = field.Type.Subst(enclosingClass.ParentFormalTypeParametersToActuals);
      if (!NeedsDefiniteAssignmentTracker(field.IsGhost || forceGhostVar, type, true)) {
        return;
      }

      var nm = SurrogateName(field);
      var tracker = localVariables.GetOrAdd(new Bpl.LocalVariable(field.Tok, new Bpl.TypedIdent(field.Tok, DefassPrefix + nm, Bpl.Type.Bool)));
      var ie = new Bpl.IdentifierExpr(field.Tok, tracker);
      DefiniteAssignmentTrackers = DefiniteAssignmentTrackers.Add(nm, ie);
    }

    void MarkDefiniteAssignmentTracker(IdentifierExpr expr, BoogieStmtListBuilder builder) {
      Contract.Requires(expr != null);
      Contract.Requires(builder != null);
      MarkDefiniteAssignmentTracker(expr.Tok, expr.Var.UniqueName, builder);
    }

    void MarkDefiniteAssignmentTracker(IOrigin tok, string name, BoogieStmtListBuilder builder) {
      Contract.Requires(tok != null);
      Contract.Requires(builder != null);

      Bpl.IdentifierExpr ie;
      if (DefiniteAssignmentTrackers.TryGetValue(name, out ie)) {
        builder.Add(Bpl.Cmd.SimpleAssign(tok, ie, Bpl.Expr.True));
      }
    }

    internal IOrigin GetToken(INode node) {
      if (flags.ReportRanges) {
        // Filter against IHasUsages to only select declarations, not usages.
        if (node is IHasNavigationToken declarationOrUsage && node is not IHasReferences) {
          return new BoogieRangeOrigin(node.StartToken, node.EndToken, declarationOrUsage.NavigationToken);
        }

        return new BoogieRangeOrigin(node.StartToken, node.EndToken, node.Tok);
      } else {
        // The commented line is what we want, but it changes what is translated.
        // Seems to relate to refinement and possibly RefinementToken.IsInherited and or ForceCheckToken
        // It might be better to remove calls to RefinementToken.IsInherited from this file, and instead
        // add generic attributes like {:verify false} in the refinement phases, so that refinement does not complicate
        // translation,
        //
        // return new BoogieRangeToken(node.StartToken, node.EndToken, node.Tok);
        return node.Tok;
      }
    }

    void CheckDefiniteAssignment(IdentifierExpr expr, BoogieStmtListBuilder builder) {
      Contract.Requires(expr != null);
      Contract.Requires(builder != null);

      Bpl.IdentifierExpr ie;
      if (DefiniteAssignmentTrackers.TryGetValue(expr.Var.UniqueName, out ie)) {
        builder.Add(Assert(GetToken(expr), ie,
          new DefiniteAssignment("variable", expr.Var.Name, "here"), builder.Context));
      }
    }

    /// <summary>
    /// Returns an expression denoting the definite-assignment tracker for "var", or "null" if there is none.
    /// </summary>
    Bpl.IdentifierExpr /*?*/ GetDefiniteAssignmentTracker(IVariable var) {
      Bpl.IdentifierExpr ie;
      if (DefiniteAssignmentTrackers.TryGetValue(var.UniqueName, out ie)) {
        return ie;
      }

      return null;
    }

    void CheckDefiniteAssignmentSurrogate(IOrigin tok, Field field, bool atNew, BoogieStmtListBuilder builder) {
      Contract.Requires(tok != null);
      Contract.Requires(field != null);
      Contract.Requires(builder != null);

      var nm = SurrogateName(field);
      if (DefiniteAssignmentTrackers.TryGetValue(nm, out var ie)) {
        var desc = new DefiniteAssignment(
          "field", field.Name, atNew ? "at this point in the constructor body" : "here");
        builder.Add(Assert(tok, ie, desc, builder.Context));
      }
    }

    void AssumeCanCallForByMethodDecl(Method method, BoogieStmtListBuilder builder) {
      if (method?.FunctionFromWhichThisIsByMethodDecl?.ByMethodTok != null && // Otherwise nothing is checked anyway
          method.Ens.Count == 1 &&
          method.Ens[0].E is BinaryExpr { E1: var e1 } &&
          e1.Resolved is FunctionCallExpr { Args: var arguments } fnCall) {
        // fnCall == (m.Ens[0].E as BinaryExpr).E1;
        // fn == new FunctionCallExpr(tok, f.Name, receiver, tok, tok, f.Formals.ConvertAll(Expression.CreateIdentExpr));
        Bpl.IdentifierExpr canCallFuncID =
          new Bpl.IdentifierExpr(method.Tok, method.FullSanitizedName + "#canCall", Bpl.Type.Bool);
        var etran = new ExpressionTranslator(this, Predef, method.Tok, method);
        List<Bpl.Expr> args = arguments.Select(arg => etran.TrExpr(arg)).ToList();
        var formals = MkTyParamBinders(GetTypeParams(method), out var tyargs);
        if (method.FunctionFromWhichThisIsByMethodDecl.ReadsHeap) {
          Contract.Assert(etran.HeapExpr != null);
          tyargs.Add(etran.HeapExpr);
        }

        if (!method.IsStatic) {
          var thVar = BplBoundVar("this", TrReceiverType(method.FunctionFromWhichThisIsByMethodDecl), out var th);
          tyargs.Add(th);
        }

        Bpl.Expr boogieAssumeCanCall =
          new Bpl.NAryExpr(method.Tok, new FunctionCall(canCallFuncID), Concat(tyargs, args));
        builder.Add(new AssumeCmd(method.Tok, boogieAssumeCanCall));
      } else {
        Contract.Assert(false, "Error in shape of by-method");
      }
    }

    void CheckDefiniteAssignmentReturn(IOrigin tok, Formal p, BoogieStmtListBuilder builder) {
      Contract.Requires(tok != null);
      Contract.Requires(p != null && !p.InParam);
      Contract.Requires(builder != null);

      Bpl.IdentifierExpr ie;
      if (DefiniteAssignmentTrackers.TryGetValue(p.UniqueName, out ie)) {
        var desc = new DefiniteAssignment("out-parameter", p.Name, "at this return point");
        builder.Add(Assert(tok, ie, desc, builder.Context));
      }
    }

    #endregion // definite-assignment tracking
  }
}
