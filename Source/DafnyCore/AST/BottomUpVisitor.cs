using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class BottomUpVisitor {
  public void Visit(IEnumerable<Expression> exprs) {
    exprs.ForEach(Visit);
  }
  public void Visit(IEnumerable<Statement> stmts) {
    stmts.ForEach(Visit);
  }
  public void Visit(AttributedExpression expr) {
    Visit(expr.E);
  }
  public void Visit(FrameExpression expr) {
    Visit(expr.E);
  }
  public void Visit(IEnumerable<AttributedExpression> exprs) {
    exprs.ForEach(Visit);
  }
  public void Visit(IEnumerable<FrameExpression> exprs) {
    exprs.ForEach(Visit);
  }
  public void Visit(ICallable decl) {
    if (decl is Function f) {
      Visit(f);
    } else if (decl is MethodOrConstructor m) {
      Visit(m);
    } else if (decl is TypeSynonymDecl tsd) {
      Visit(tsd);
    } else if (decl is NewtypeDecl ntd) {
      Visit(ntd);
    }
    //TODO More?
  }

  public void Visit(SubsetTypeDecl ntd) {
    if (ntd.Constraint != null) {
      Visit(ntd.Constraint);
    }

    if (ntd.Witness != null) {
      Visit(ntd.Witness);
    }
  }
  public void Visit(NewtypeDecl ntd) {
    if (ntd.Constraint != null) {
      Visit(ntd.Constraint);
    }

    if (ntd.Witness != null) {
      Visit(ntd.Witness);
    }
  }
  public void Visit(MethodOrConstructor method) {
    Visit(method.Req);
    Visit(method.Reads.Expressions);
    Visit(method.Mod.Expressions);
    Visit(method.Ens);
    Visit(method.Decreases.Expressions);
    if (method.Body != null) { Visit(method.Body); }
    //TODO More?
  }
  public void Visit(Function function) {
    Visit(function.Req);
    Visit(function.Reads.Expressions);
    Visit(function.Ens);
    Visit(function.Decreases.Expressions);
    if (function.Body != null) { Visit(function.Body); }
    if (function.ByMethodBody != null) { Visit(function.ByMethodBody); }
    //TODO More?
  }
  public void Visit(Expression expr) {
    Contract.Requires(expr != null);
    // recursively visit all subexpressions and all substatements
    expr.SubExpressions.ForEach(Visit);
    if (expr is StmtExpr) {
      // a StmtExpr also has a substatement
      var e = (StmtExpr)expr;
      Visit(e.S);
    }
    VisitOneExpr(expr);
  }
  public void Visit(Statement stmt) {
    Contract.Requires(stmt != null);
    // recursively visit all subexpressions and all substatements
    stmt.SubExpressions.ForEach(Visit);
    stmt.SubStatements.ForEach(Visit);
    VisitOneStmt(stmt);
  }
  protected virtual void VisitOneExpr(Expression expr) {
    Contract.Requires(expr != null);
    // by default, do nothing
  }
  protected virtual void VisitOneStmt(Statement stmt) {
    Contract.Requires(stmt != null);
    // by default, do nothing
  }
}