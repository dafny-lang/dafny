using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Function = Microsoft.Dafny.Function;
using Program = Microsoft.Dafny.Program;
using Type = Microsoft.Dafny.Type;


namespace DafnyTestGeneration.Inlining; 

public class FunctionCallToMethodCallRewriter: Cloner {

  public FunctionCallToMethodCallRewriter() : base(false, true) { }
  
  public void Visit(Program program) {
    Visit(program.DefaultModule);
  }

  public void Visit(TopLevelDecl d) {
    if (d is LiteralModuleDecl moduleDecl) {
      moduleDecl.ModuleDef.TopLevelDecls.Iter(Visit);
    } else if (d is TopLevelDeclWithMembers withMembers) {
      withMembers.Members.OfType<Microsoft.Dafny.Function>().Iter(Visit);
      withMembers.Members.OfType<Method>().Iter(Visit);
    }
  }

  public void Visit(Function function) {
    if (function.ByMethodBody != null && !function.IsGhost) {
      Visit(function.ByMethodBody);
    }
  }

  public void Visit(Method method) {
    if (method.Body != null && !method.IsGhost) {
      Visit(method.Body);
    }
  }

  private void Visit(BlockStmt blockStatement) {
    for (int i = 0; i < blockStatement.Body.Count; i++) {
      var stmt = blockStatement.Body[i];
      blockStatement.Body.RemoveAt(i);
      blockStatement.Body.Insert(i, CloneStmt(stmt));
    }
  }

  public override Statement CloneStmt(Statement stmt) {
    if (stmt == null) {
      return null;
    }
    if (stmt.IsGhost || stmt is not UpdateStmt updateStmt) {
      return base.CloneStmt(stmt);
    }
    var clonedUpdate = (UpdateStmt) base.CloneStmt(updateStmt);
    var newResolvedStmts = new List<Statement>();
    var madeChanges = false;
    foreach (var resolvedStmt in updateStmt.ResolvedStatements) {
      if (!resolvedStmt.IsGhost &&
          resolvedStmt is AssignStmt assignStmt &&
          assignStmt.Rhs is ExprRhs exprRhs &&
          exprRhs.Expr.Resolved is FunctionCallExpr funcCallExpr &&
          funcCallExpr.IsByMethodCall) {
        var memberSelectExpr = new MemberSelectExpr(funcCallExpr.tok, CloneExpr(funcCallExpr.Receiver.Resolved), funcCallExpr.Function.ByMethodDecl.Name);
        memberSelectExpr.Member = funcCallExpr.Function.ByMethodDecl;
        memberSelectExpr.TypeApplication_JustMember = funcCallExpr.TypeApplication_JustFunction;
        madeChanges = true;
        newResolvedStmts.Add(new CallStmt(stmt.RangeToken, updateStmt.Lhss.Select(lhs => CloneExpr(lhs.Resolved)).ToList(), memberSelectExpr, funcCallExpr.Args.Select(CloneExpr).ToList()));
      } else {
        newResolvedStmts.Add(resolvedStmt);
      }
    }

    if (madeChanges) {
      clonedUpdate.ResolvedStatements = newResolvedStmts;
    }

    return clonedUpdate;
  }
}