// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Function = Microsoft.Dafny.Function;
using Program = Microsoft.Dafny.Program;


namespace DafnyTestGeneration.Inlining; 

/// <summary>
/// Change by-method function calls to method calls (after resolution)
/// </summary>
public class FunctionCallToMethodCallCloner : Cloner {
  
  // determines whether function calls should be replaced with method calls in a given method/function
  private readonly Func<MemberDecl, bool> shouldProcessPredicate;

  public FunctionCallToMethodCallCloner(Func<MemberDecl, bool> shouldProcessPredicate) : base(false, true) {
    this.shouldProcessPredicate = shouldProcessPredicate;
  }

  public void Visit(Program program) {
    Visit(program.DefaultModule);
  }

  private void Visit(TopLevelDecl d) {
    if (d is LiteralModuleDecl moduleDecl) {
      moduleDecl.ModuleDef.TopLevelDecls.Iter(Visit);
    } else if (d is TopLevelDeclWithMembers withMembers) {
      withMembers.Members.Where(shouldProcessPredicate).OfType<Function>().Iter(Visit);
      withMembers.Members.Where(shouldProcessPredicate).OfType<Method>().Iter(Visit);
    }
  }

  private void Visit(Function function) {
    if (function.ByMethodBody != null && !function.IsGhost) {
      function.ByMethodBody = CloneBlockStmt(function.ByMethodBody);
    }
  }

  private void Visit(Method method) {
    if (method.Body == null || method.IsGhost) {
      return;
    }
    if (method.Body is DividedBlockStmt dividedBlockStmt) {
      method.Body = CloneDividedBlockStmt(dividedBlockStmt);
    } else {
      method.Body = CloneBlockStmt(method.Body);
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
    if (stmt == null || stmt.IsGhost || stmt is not UpdateStmt updateStmt) {
      return base.CloneStmt(stmt);
    }
    var clonedUpdate = (UpdateStmt)base.CloneStmt(updateStmt);
    var newResolvedStmts = new List<Statement>();
    foreach (var resolvedStmt in clonedUpdate.ResolvedStatements) {
      if (!resolvedStmt.IsGhost &&
          resolvedStmt is AssignStmt { Rhs: ExprRhs exprRhs } &&
          exprRhs.Expr.Resolved is FunctionCallExpr { IsByMethodCall: true } funcCallExpr) {
        var memberSelectExpr = new MemberSelectExpr(
          funcCallExpr.tok,
          CloneExpr(funcCallExpr.Receiver.Resolved),
          funcCallExpr.Function.ByMethodDecl.Name);
        memberSelectExpr.Member = funcCallExpr.Function.ByMethodDecl;
        memberSelectExpr.TypeApplication_JustMember = funcCallExpr.TypeApplication_JustFunction;
        newResolvedStmts.Add(new CallStmt(stmt.RangeToken,
          updateStmt.Lhss.Select(lhs => CloneExpr(lhs.Resolved)).ToList(), memberSelectExpr,
          funcCallExpr.Args.ConvertAll(e => CloneExpr(e.Resolved))));
      } else {
        newResolvedStmts.Add(resolvedStmt);
      }
    }
    clonedUpdate.ResolvedStatements = newResolvedStmts;
    return clonedUpdate;
  }
}