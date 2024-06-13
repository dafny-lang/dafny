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

  Expr TrStmtSideEffect(Expr e, Statement stmt, ExpressionTranslator etran) {
    if (stmt is CallStmt) {
      var call = (CallStmt)stmt;
      var m = call.Method;
      if (IsOpaqueRevealLemma(m)) {
        List<Expression> args = Attributes.FindExpressions(m.Attributes, "fuel");
        if (args != null) {
          MemberSelectExpr selectExpr = args[0].Resolved as MemberSelectExpr;
          if (selectExpr != null) {
            Function f = selectExpr.Member as Function;
            FuelConstant fuelConstant = this.functionFuel.Find(x => x.f == f);
            if (fuelConstant != null) {
              Bpl.Expr startFuel = fuelConstant.startFuel;
              Bpl.Expr startFuelAssert = fuelConstant.startFuelAssert;
              Bpl.Expr moreFuel_expr = fuelConstant.MoreFuel(sink, predef, f.IdGenerator);
              Bpl.Expr layer = etran.layerInterCluster.LayerN(1, moreFuel_expr);
              Bpl.Expr layerAssert = etran.layerInterCluster.LayerN(2, moreFuel_expr);

              e = BplAnd(e, Bpl.Expr.Eq(startFuel, layer));
              e = BplAnd(e, Bpl.Expr.Eq(startFuelAssert, layerAssert));
              e = BplAnd(e, Bpl.Expr.Eq(this.FunctionCall(f.tok, BuiltinFunction.AsFuelBottom, null, moreFuel_expr), moreFuel_expr));
            }
          }
        }
      }
    } else if (stmt is RevealStmt reveal) {
      foreach (var s in reveal.ResolvedStatements) {
        e = BplAnd(e, TrFunctionSideEffect(s, etran));
      }
    }
    return e;
  }
}
