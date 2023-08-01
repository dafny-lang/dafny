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

  private bool CrawlAndCheck(Func<Type, Boolean> check, Type rhs) {
    Type type = rhs.NormalizeExpandKeepConstraints();
    if (type is BasicType) {
      return false;
    } else if (type is MapType) {
      var t = (MapType)type;
      return CrawlAndCheck(check, t.Domain) || CrawlAndCheck(check, t.Range);
    } else if (type is CollectionType) {
      var t = (CollectionType)type;
      return CrawlAndCheck(check, t.Arg);
    } else {
      var t = (UserDefinedType)type;
      if (check(t)) {
        return true;
      }

      var b = false;
      for (int i = 0; i < t.TypeArgs.Count; i++) {
        b = b || CrawlAndCheck(check, t.TypeArgs[i]);
      }

      return b;
    }
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

  private bool OccursSquig(Type rhs) {
    Type type = rhs.NormalizeExpandKeepConstraints();
    if (type is BasicType) {
      return false;
    } else if (type is MapType) {
      var t = (MapType)type;
      return OccursSquig(t.Domain) || OccursSquig(t.Range);
    } else if (type is CollectionType) {
      var t = (CollectionType)type;
      return OccursSquig(t.Arg);
    } else {
      var t = (UserDefinedType)type;
      if (t.IsArrowType) {
        if (!t.IsArrowTypeWithoutReadEffects) {
          return true;
        }
      }

      var b = false;
      for (int i = 0; i < t.TypeArgs.Count; i++) {
        b = b || OccursSquig(t.TypeArgs[i]);
      }

      return b;
    }
  }

  protected override bool VisitOneStatement(Statement stmt, IASTVisitorContext context) {
    if (stmt is AssignStmt assign) {

      var lhs = assign.Lhs;
      Type lhsType;
      if (lhs is MemberSelectExpr mseLhs) {
        lhsType = mseLhs.Obj.Type.NormalizeExpandKeepConstraints();
      } else if (lhs is SeqSelectExpr sseLhs) {
        lhsType = sseLhs.Type.NormalizeExpandKeepConstraints();
      } else {
        return base.VisitOneStatement(stmt, context);
      }

      var rhs = assign.Rhs;
      if (rhs is ExprRhs eRhs) {
        var exp = eRhs.Expr;
        var type = exp.Type;

        //if (OccursSquig(type)) {
        if (CrawlAndCheck(t => !t.IsArrowTypeWithoutReadEffects, type)) {
          reporter.Error(MessageSource.Resolver, stmt,
            $"To prevent the creation of non-terminating functions, storing functions with read effects into memory is disallowed");
        }

        if (type.IsArrowType) {

          var arrow = type.AsArrowType;
          for (int i = 0; i < arrow.Arity; i++) {
            //var occurs = Occurs(lhsType, arrow.Args[i]);
            var occurs = Occurs(lhsType, arrow.Args[i]);
            if (CrawlAndCheck(t => lhsType.Equals(t), arrow.Args[i])) {
              reporter.Error(MessageSource.Resolver, stmt,
                $"To prevent the creation of non-terminating functions, storing functions into an object's fields that reads the object is disallowed");
            }
          }
        }
      }
    }

    return base.VisitOneStatement(stmt, context);
  }
}