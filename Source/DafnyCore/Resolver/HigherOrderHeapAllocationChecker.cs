//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
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

  private bool ContainsRead(Type rhs) {
    Type type = rhs.NormalizeExpandKeepConstraints();
    if (type is BasicType) {
      return false;
    } else if (type is MapType) {
      var t = (MapType)type;
      return ContainsRead(t.Domain) || ContainsRead(t.Range);
    } else if (type is CollectionType) {
      var t = (CollectionType)type;
      return ContainsRead(t.Arg);
    } else {
      var t = (UserDefinedType)type;
      if (t.IsArrowType) {
        if (!t.IsArrowTypeWithoutReadEffects) {
          return true;
        }
      }

      var b = false;
      for (int i = 0; i < t.TypeArgs.Count; i++) {
        b = b || ContainsRead(t.TypeArgs[i]);
      }

      return b;
    }
  }

  protected override bool VisitOneStatement(Statement stmt, IASTVisitorContext context) {
    if (stmt is AssignStmt assign) {

      var lhs = assign.Lhs;
      var rhs = assign.Rhs;
      if (lhs is MemberSelectExpr || lhs is SeqSelectExpr) {

        if (rhs is ExprRhs eRhs) {
          var exp = eRhs.Expr;
          var type = exp.Type;

          if (ContainsRead(type)) {
            reporter.Error(MessageSource.Resolver, stmt,
              $"To prevent the creation of non-terminating functions, storing functions with read effects into memory is disallowed");
          }
        }
      }
    }

    return base.VisitOneStatement(stmt, context);
  }
}