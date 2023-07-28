//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Reflection;

namespace Microsoft.Dafny;

class HigherOrderHeapAllocationChecker : ASTVisitor<IASTVisitorContext> {
  private readonly ErrorReporter reporter;

  public HigherOrderHeapAllocationChecker(ErrorReporter reporter) {
    this.reporter = reporter;
  }

  public override IASTVisitorContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
    return astVisitorContext;
  }

  protected override bool VisitOneStatement(Statement stmt, IASTVisitorContext context) {
    if (stmt is AssignStmt assign) {
      var rhs = assign.Rhs;
      var lhs = assign.Lhs;
      if (lhs is MemberSelectExpr mseLhs) {
        if (rhs is ExprRhs eRhs) {
          var exp = eRhs.Expr;
          var type = exp.Type;
          if (type.IsArrowType) {
            if (!type.IsArrowTypeWithoutReadEffects) {
              reporter.Error(MessageSource.Resolver, stmt,
                $"Illegal");
            }
          }
        }
      }
    }
    return base.VisitOneStatement(stmt, context);
  }
}