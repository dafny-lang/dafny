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

  private bool Occurs(Type Obj, Type rhs) {
    Type type = rhs.NormalizeExpandKeepConstraints();
    if (type is BasicType) {
      return false;
    } else if (type is MapType) {
      var t = (MapType)type;
      return Occurs(Obj, t.Domain) || Occurs(Obj, t.Range);
    } else if (type is CollectionType) {
      var t = (CollectionType)type;
      return Occurs(Obj, t.Arg);
    } else {
      var t = (UserDefinedType)type;
      if (Obj.Equals(t)) {
        return true;
      }
      var b = false;
      for (int i = 0; i < t.TypeArgs.Count; i++) {
        b = b || Occurs(Obj, t.TypeArgs[i]);
      }
      return b;
    }
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
              reporter.Error(MessageSource.Resolver, stmt, $"Illegal 1");
            }

            var arrow = type.AsArrowType;
            for (int i = 0; i < arrow.Arity; i++) {
              var occurs = Occurs(mseLhs.Obj.Type.NormalizeExpandKeepConstraints(), arrow.Args[i]);
              if (occurs) { // mseLhs.Obj.Type.Equals(arrow.Args[0])
                reporter.Error(MessageSource.Resolver, stmt, $"Illegal 2");
              }
            }

          }

        }
      }
    }
    return base.VisitOneStatement(stmt, context);
  }
}