using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using Bpl = Microsoft.Boogie;
using PODesc = Microsoft.Dafny.ProofObligationDescription;
using static Microsoft.Dafny.GenericErrors;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {

  // Cache to store translated expressions by label name for issue #6268 fix
  public static readonly Dictionary<string, Boogie.Expr> LabelExpressionCache = new();

  private static void TranslateRevealStmt(BoogieGenerator boogieGenerator, BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran,
    HideRevealStmt revealStmt) {
    AddComment(builder, revealStmt, "hide/reveal statement");
    foreach (var la in revealStmt.LabeledAsserts) {
      // ROOT CAUSE FIX for issue #6268: We're accessing the wrong AssertLabel object!
      // The assert statement fills E on one object, but reveal accesses a different cloned object.
      // We use a cache to find the correct translated expression by label name.
      Boogie.Expr exprToUse = la.E;
      if (exprToUse == null && la.Name != null) {
        // Try to find the cached expression for this label name
        exprToUse = FindFilledExpressionForLabel(boogieGenerator, la.Name);
      }
      
      if (exprToUse != null) {
        builder.Add(new AssumeCmd(revealStmt.Origin, exprToUse));
      }
    }

    if (builder.Context.ContainsHide) {
      if (revealStmt.Wildcard) {
        builder.Add(new HideRevealCmd(revealStmt.Origin, revealStmt.Mode));
      } else {
        foreach (var member in revealStmt.OffsetMembers) {
          builder.Add(new HideRevealCmd(new Bpl.IdentifierExpr(revealStmt.Origin, member.FullSanitizedName), revealStmt.Mode));
        }
      }
    }

    boogieGenerator.TrStmtList(revealStmt.ResolvedStatements, builder, locals, etran);
  }

  // Helper to find the AssertLabel object that actually has the E field filled
  private static Boogie.Expr FindFilledExpressionForLabel(BoogieGenerator generator, string labelName) {
    // Look up the cached expression for this label name
    LabelExpressionCache.TryGetValue(labelName, out var cachedExpr);
    return cachedExpr;
  }

  Expr TrStmtSideEffect(Expr e, Statement stmt, ExpressionTranslator etran) {
    switch (stmt) {
      case CallStmt call: {
          var m = call.Method;
          if (!IsOpaqueRevealLemma(m)) {
            return e;
          }

          var args = Attributes.FindExpressions(m.Attributes, "fuel");
          if (args == null) {
            return e;
          }

          if (args[0].Resolved is not MemberSelectExpr selectExpr) {
            return e;
          }

          var f = selectExpr.Member as Function;
          var fuelConstant = functionFuel.Find(x => x.f == f);
          if (fuelConstant == null) {
            return e;
          }

          var startFuel = fuelConstant.startFuel;
          var startFuelAssert = fuelConstant.startFuelAssert;
          var moreFuelExpr = fuelConstant.MoreFuel(sink, Predef, f.IdGenerator);
          var layer = etran.layerInterCluster.LayerN(1, moreFuelExpr);
          var layerAssert = etran.layerInterCluster.LayerN(2, moreFuelExpr);

          e = BplAnd(e, Expr.Eq(startFuel, layer));
          e = BplAnd(e, Expr.Eq(startFuelAssert, layerAssert));
          e = BplAnd(e, Expr.Eq(FunctionCall(f.Origin, BuiltinFunction.AsFuelBottom, null, moreFuelExpr), moreFuelExpr));

          return e;
        }
      case HideRevealStmt reveal: {
          foreach (var s in reveal.ResolvedStatements) {
            e = BplAnd(e, TrFunctionSideEffect(s, etran));
          }

          return e;
        }
      default: return e;
    }
  }
}
