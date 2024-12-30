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
public class FunctionCallToMethodCallRewriter : Cloner {

  // determines whether function calls should be replaced with method calls in a given method/function
  private readonly Func<MemberDecl, bool> shouldProcessPredicate;

  public FunctionCallToMethodCallRewriter(Func<MemberDecl, bool> shouldProcessPredicate) : base(false, true) {
    this.shouldProcessPredicate = shouldProcessPredicate;
  }

  public void PostResolve(Program program) {
    Visit(program.DefaultModule);
  }

  private void Visit(TopLevelDecl d) {
    if (d is LiteralModuleDecl moduleDecl) {
      moduleDecl.ModuleDef.Children.OfType<TopLevelDecl>().ForEach(Visit);
    } else if (d is TopLevelDeclWithMembers withMembers) {
      withMembers.Members.Where(shouldProcessPredicate).OfType<Function>().ForEach(Visit);
      withMembers.Members.Where(shouldProcessPredicate).OfType<Method>().ForEach(Visit);
    }
  }

  private void Visit(Function function) {
    if (function.ByMethodBody != null) {
      function.ByMethodBody = CloneBlockStmt(function.ByMethodBody);
      function.ByMethodDecl.Body = function.ByMethodBody;
    }
  }

  private void Visit(Method method) {
    if (method.Body != null) {
      if (method.Body is DividedBlockStmt dividedBlockStmt) {
        method.Body = CloneDividedBlockStmt(dividedBlockStmt);
      } else {
        method.Body = CloneBlockStmt(method.Body);
      }
    }
  }

  public override Statement CloneStmt(Statement stmt, bool isReference) {
    if (stmt == null || stmt is not AssignStatement updateStmt) {
      return base.CloneStmt(stmt, isReference);
    }
    var clonedUpdate = (AssignStatement)base.CloneStmt(updateStmt, isReference);
    var newResolvedStmts = new List<Statement>();
    foreach (var resolvedStmt in clonedUpdate.ResolvedStatements) {
      if (!resolvedStmt.IsGhost &&
          resolvedStmt is SingleAssignStmt { Rhs: ExprRhs exprRhs } &&
          exprRhs.Expr.Resolved is FunctionCallExpr { IsByMethodCall: true } funcCallExpr) {
        var memberSelectExpr = new MemberSelectExpr(
          funcCallExpr.Tok,
          CloneExpr(funcCallExpr.Receiver.Resolved),
          funcCallExpr.Function.ByMethodDecl.NameNode);
        memberSelectExpr.Member = funcCallExpr.Function.ByMethodDecl;
        memberSelectExpr.TypeApplicationJustMember = funcCallExpr.TypeApplication_JustFunction;
        newResolvedStmts.Add(new CallStmt(stmt.Origin,
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