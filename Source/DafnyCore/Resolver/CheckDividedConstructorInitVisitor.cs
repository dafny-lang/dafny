using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

class CheckDividedConstructorInitVisitor : ResolverTopDownVisitor<int> {
  public CheckDividedConstructorInitVisitor(ErrorReporter reporter)
    : base(reporter) {
    Contract.Requires(reporter != null);
  }
  public void CheckInit(List<Statement> initStmts) {
    Contract.Requires(initStmts != null);
    initStmts.ForEach(CheckInit);
  }
  /// <summary>
  /// This method almost does what Visit(Statement) does, except that it handles assignments to
  /// fields differently.
  /// </summary>
  void CheckInit(Statement stmt) {
    Contract.Requires(stmt != null);
    // Visit(stmt) would do:
    //     stmt.SubExpressions.Iter(Visit);    (*)
    //     stmt.SubStatements.Iter(Visit);     (**)
    //     VisitOneStmt(stmt);                 (***)
    // We may do less for (*), we always use CheckInit instead of Visit in (**), and we do (***) the same.
    if (stmt is SingleAssignStmt) {
      var s = stmt as SingleAssignStmt;
      // The usual visitation of s.SubExpressions.Iter(Visit) would do the following:
      //   Attributes.SubExpressions(s.Attributes).Iter(Visit);  (+)
      //   Visit(s.Lhs);                                         (++)
      //   s.Rhs.SubExpressions.Iter(Visit);                     (+++)
      // Here, we may do less; in particular, we may omit (++).
      Attributes.SubExpressions(s.Attributes).ForEach(VisitExpr);  // (+)
      var mse = s.Lhs as MemberSelectExpr;
      if (mse != null && Expression.AsThis(mse.Obj) != null) {
        if (s.Rhs is ExprRhs) {
          // This is a special case we allow.  Omit s.Lhs in the recursive visits.  That is, we omit (++).
          // Furthermore, because the assignment goes to a field of "this" and won't be available until after
          // the "new;", we can allow certain specific (and useful) uses of "this" in the RHS.
          s.Rhs.SubExpressions.ForEach(LiberalRHSVisit);  // (+++)
        } else {
          s.Rhs.SubExpressions.ForEach(VisitExpr);  // (+++)
        }
      } else {
        VisitExpr(s.Lhs);  // (++)
        s.Rhs.SubExpressions.ForEach(VisitExpr);  // (+++)
      }
    } else {
      stmt.SubExpressions.ForEach(VisitExpr);  // (*)
    }
    stmt.SubStatements.ForEach(CheckInit);  // (**)
    int dummy = 0;
    VisitOneStmt(stmt, ref dummy);  // (***)
  }
  void VisitExpr(Expression expr) {
    Contract.Requires(expr != null);
    Visit(expr, 0);
  }
  protected override bool VisitOneExpr(Expression expr, ref int unused) {
    if (expr is MemberSelectExpr) {
      var e = (MemberSelectExpr)expr;
      if (e.Member.IsInstanceIndependentConstant && Expression.AsThis(e.Obj) != null) {
        return false;  // don't continue the recursion
      }
    } else if (expr is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Assigned }) {
      return false;  // don't continue the recursion
    } else if (expr is ThisExpr && !(expr is ImplicitThisExprConstructorCall)) {
      reporter.Error(MessageSource.Resolver, expr.Origin, "in the first division of the constructor body (before 'new;'), 'this' can only be used to assign to its fields");
    }
    return base.VisitOneExpr(expr, ref unused);
  }
  void LiberalRHSVisit(Expression expr) {
    Contract.Requires(expr != null);
    // It is important not to allow "this" to flow into something that can be used (for compilation or
    // verification purposes) before the "new;", because, to the verifier, "this" has not yet been allocated.
    // The verifier is told that everything reachable from the heap is expected to be allocated and satisfy all
    // the usual properties, so "this" had better not become reachable from the heap until after the "new;"
    // that does the actual allocation of "this".
    // Within these restrictions, we can allow the (not yet fully available) value "this" to flow into values
    // stored in fields of "this".  Such values are naked occurrences of "this" and "this" occurring
    // as part of constructing a value type.  Since by this rule, "this" may be part of the value stored in
    // a field of "this", we must apply the same rules to uses of the values of fields of "this".
    if (expr is ConcreteSyntaxExpression) {
    } else if (expr is ThisExpr) {
    } else if (expr is MemberSelectExpr && IsThisDotField((MemberSelectExpr)expr)) {
    } else if (expr is SetDisplayExpr) {
    } else if (expr is MultiSetDisplayExpr) {
    } else if (expr is SeqDisplayExpr) {
    } else if (expr is MapDisplayExpr) {
    } else if (expr is BinaryExpr && IsCollectionOperator(((BinaryExpr)expr).ResolvedOp)) {
    } else if (expr is DatatypeValue) {
    } else if (expr is ITEExpr) {
      var e = (ITEExpr)expr;
      VisitExpr(e.Test);
      LiberalRHSVisit(e.Thn);
      LiberalRHSVisit(e.Els);
      return;
    } else {
      // defer to the usual Visit
      VisitExpr(expr);
      return;
    }
    expr.SubExpressions.ForEach(LiberalRHSVisit);
  }
  static bool IsThisDotField(MemberSelectExpr expr) {
    Contract.Requires(expr != null);
    return Expression.AsThis(expr.Obj) != null && expr.Member is Field;
  }
  static bool IsCollectionOperator(BinaryExpr.ResolvedOpcode op) {
    switch (op) {
      // sets:  +, *, -
      case BinaryExpr.ResolvedOpcode.Union:
      case BinaryExpr.ResolvedOpcode.Intersection:
      case BinaryExpr.ResolvedOpcode.SetDifference:
      // multisets: +, *, -
      case BinaryExpr.ResolvedOpcode.MultiSetUnion:
      case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
      case BinaryExpr.ResolvedOpcode.MultiSetDifference:
      // sequences: +
      case BinaryExpr.ResolvedOpcode.Concat:
      // maps: +, -
      case BinaryExpr.ResolvedOpcode.MapMerge:
      case BinaryExpr.ResolvedOpcode.MapSubtraction:
        return true;
      default:
        return false;
    }
  }
}