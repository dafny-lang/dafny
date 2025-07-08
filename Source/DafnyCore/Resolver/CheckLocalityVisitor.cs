using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

class CheckLocalityVisitor : ResolverBottomUpVisitor {
  readonly ICodeContext codeContext;
  public CheckLocalityVisitor(ModuleResolver resolver, ICodeContext codeContext)
    : base(resolver) {
    Contract.Requires(resolver != null);
    Contract.Requires(codeContext != null);
    this.codeContext = codeContext;
  }
  protected override void VisitOneExpr(Expression expr) {
    if (expr is StmtExpr) {
      var e = (StmtExpr)expr;
      resolver.ComputeGhostInterest(e.S, true, "a statement expression", codeContext);
    } else if (expr is LetExpr) {
      var e = (LetExpr)expr;
      if (codeContext.IsGhost) {
        foreach (var bv in e.BoundVars) {
          bv.MakeGhost();
        }
      }
    }
  }

  protected override void VisitOneStmt(Statement stmt) {
    switch (stmt) {
      case CalcStmt calc: {
          foreach (var h in calc.Hints) {
            resolver.CheckLocalityUpdates(h, new HashSet<LocalVariable>(), "a hint");
          }

          break;
        }
      case BlockByProofStmt blockByProofStmt:
        resolver.CheckLocalityUpdates(blockByProofStmt.Proof, new HashSet<LocalVariable>(), "a by block");
        break;
      case ForallStmt { Body: not null } forall:
        resolver.CheckLocalityUpdates(forall.Body, new HashSet<LocalVariable>(), "a forall statement");
        break;
    }
  }
}