using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

class ExtremePredicateChecksVisitor : FindFriendlyCallsVisitor {
  readonly ExtremePredicate context;
  public ExtremePredicateChecksVisitor(ErrorReporter reporter, ExtremePredicate context)
    : base(reporter, context is GreatestPredicate, context.KNat) {
    Contract.Requires(reporter != null);
    Contract.Requires(context != null);
    this.context = context;
  }
  protected override bool VisitOneExpr(Expression expr, ref CallingPosition cp) {
    if (expr is FunctionCallExpr) {
      var e = (FunctionCallExpr)expr;
      if (ModuleDefinition.InSameSCC(context, e.Function)) {
        // we're looking at a recursive call
        if (!(context is LeastPredicate ? e.Function is LeastPredicate : e.Function is GreatestPredicate)) {
          reporter.Error(MessageSource.Resolver, e, "a recursive call from a {0} can go only to other {0}s", context.WhatKind);
        } else if (context.KNat != ((ExtremePredicate)e.Function).KNat) {
          KNatMismatchError(e.Origin, context.Name, context.TypeOfK, ((ExtremePredicate)e.Function).TypeOfK);
        } else if (cp != CallingPosition.Positive) {
          var msg = $"a {context.WhatKind} can be called recursively only in positive positions";
          if (ContinuityIsImportant && cp == CallingPosition.Neither) {
            // this may be inside an non-friendly quantifier
            msg +=
              $" and cannot sit inside an unbounded {(context is LeastPredicate ? "universal" : "existential")} quantifier";
          } else {
            // we don't care about the continuity restriction or
            // the extreme-call is not inside an quantifier, so don't bother mentioning the part of existentials/universals in the error message
          }
          reporter.Error(MessageSource.Resolver, e, msg);
        } else {
          e.CoCall = FunctionCallExpr.CoCallResolution.Yes;
          reporter.Info(MessageSource.Resolver, e.Origin, e.Function.Name + "#[_k - 1]");
        }
      }
      // do the sub-parts with cp := Neither
      cp = CallingPosition.Neither;
      return true;
    }
    return base.VisitOneExpr(expr, ref cp);
  }
  protected override bool VisitOneStmt(Statement stmt, ref CallingPosition st) {
    if (stmt is CallStmt) {
      var s = (CallStmt)stmt;
      if (ModuleDefinition.InSameSCC(context, s.Method)) {
        // we're looking at a recursive call
        reporter.Error(MessageSource.Resolver, stmt.Origin, "a recursive call from a {0} can go only to other {0}s", context.WhatKind);
      }
      // do the sub-parts with the same "cp"
      return true;
    } else {
      return base.VisitOneStmt(stmt, ref st);
    }
  }
}