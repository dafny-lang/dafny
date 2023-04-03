using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class Abstemious {
  private readonly ErrorReporter reporter;

  public Abstemious(ErrorReporter reporter) {
    this.reporter = reporter;
  }

  public void Check(Function fn) {
    if (fn.Body != null) {
      var abstemious = true;
      if (Attributes.ContainsBool(fn.Attributes, "abstemious", ref abstemious) && abstemious) {
        if (CoCallResolution.GuaranteedCoCtors(fn) == 0) {
          reporter.Error(MessageSource.Resolver, fn, "the value returned by an abstemious function must come from invoking a co-constructor");
        } else {
          CheckDestructsAreAbstemiousCompliant(fn.Body);
        }
      }
    }
  }

  private void CheckDestructsAreAbstemiousCompliant(Expression expr) {
    Contract.Assert(expr != null);
    expr = expr.Resolved;
    if (expr is MemberSelectExpr) {
      var e = (MemberSelectExpr)expr;
      if (e.Member.EnclosingClass is CoDatatypeDecl) {
        var ide = Expression.StripParens(e.Obj).Resolved as IdentifierExpr;
        if (ide != null && ide.Var is Formal) {
          // cool
        } else {
          reporter.Error(MessageSource.Resolver, expr, "an abstemious function is allowed to invoke a codatatype destructor only on its parameters");
        }
        return;
      }
    } else if (expr is NestedMatchExpr nestedMatchExpr) {
      if (nestedMatchExpr.Source.Type.IsCoDatatype) {
        var ide = Expression.StripParens(nestedMatchExpr.Source).Resolved as IdentifierExpr;
        if (ide != null && ide.Var is Formal) {
          // cool; fall through to check match branches
        } else {
          reporter.Error(MessageSource.Resolver, nestedMatchExpr.Source, "an abstemious function is allowed to codatatype-match only on its parameters");
          return;
        }
      }
    } else if (expr is MatchExpr) {
      var e = (MatchExpr)expr;
      if (e.Source.Type.IsCoDatatype) {
        var ide = Expression.StripParens(e.Source).Resolved as IdentifierExpr;
        if (ide != null && ide.Var is Formal) {
          // cool; fall through to check match branches
        } else {
          reporter.Error(MessageSource.Resolver, e.Source, "an abstemious function is allowed to codatatype-match only on its parameters");
          return;
        }
      }
    } else if (expr is BinaryExpr) {
      var e = (BinaryExpr)expr;
      if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || e.ResolvedOp == BinaryExpr.ResolvedOpcode.NeqCommon) {
        if (e.E0.Type.IsCoDatatype) {
          reporter.Error(MessageSource.Resolver, expr, "an abstemious function is not only allowed to check codatatype equality");
          return;
        }
      }
    } else if (expr is StmtExpr) {
      var e = (StmtExpr)expr;
      // ignore the statement part
      CheckDestructsAreAbstemiousCompliant(e.E);
      return;
    }
    expr.SubExpressions.Iter(CheckDestructsAreAbstemiousCompliant);
  }
}