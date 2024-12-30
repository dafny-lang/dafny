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

  private static void TranslateRevealStmt(BoogieGenerator boogieGenerator, BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran,
    HideRevealStmt revealStmt) {
    AddComment(builder, revealStmt, "hide/reveal statement");
    foreach (var la in revealStmt.LabeledAsserts) {
      Contract.Assert(la.E != null);  // this should have been filled in by now
      builder.Add(new AssumeCmd(revealStmt.Tok, la.E));
    }

    if (builder.Context.ContainsHide) {
      if (revealStmt.Wildcard) {
        builder.Add(new HideRevealCmd(revealStmt.Tok, revealStmt.Mode));
      } else {
        foreach (var member in revealStmt.OffsetMembers) {
          builder.Add(new HideRevealCmd(new Bpl.IdentifierExpr(revealStmt.Tok, member.FullSanitizedName), revealStmt.Mode));
        }
      }
    }

    boogieGenerator.TrStmtList(revealStmt.ResolvedStatements, builder, locals, etran);
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
          e = BplAnd(e, Expr.Eq(FunctionCall(f.Tok, BuiltinFunction.AsFuelBottom, null, moreFuelExpr), moreFuelExpr));

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
