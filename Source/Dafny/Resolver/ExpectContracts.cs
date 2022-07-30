using System;
using System.Collections.Generic;
using System.Data;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Microsoft.Dafny; 

public class ExpectContracts : IRewriter {
  private readonly ClonerButDropMethodBodies cloner = new();

  public ExpectContracts(ErrorReporter reporter) : base(reporter) {
  }

  /// <summary>
  /// Create an expect statement that checks the given contract clause
  /// expression and fails with a message that points to the original
  /// location of the contract clause if it is not true at runtime.
  /// </summary>
  /// <param name="expr">The contract clause expression to evaluate.</param>
  /// <param name="exprType">Either "requires" or "ensures", to use in the
  /// failure message.</param>
  /// <returns>The newly-created expect statement.</returns>
  private static Statement CreateContractExpectStatement(AttributedExpression expr, string exprType) {
    var tok = expr.E.tok;
    var msg = $"Runtime failure of {exprType} clause from {tok.filename}:{tok.line}:{tok.col}";
    var msgExpr = Expression.CreateStringLiteral(tok, msg);
    return new ExpectStmt(tok, expr.E.EndToken, expr.E, msgExpr, null);
  }

  /// <summary>
  /// Creates a block statement that includes an expect statement for every
  /// requires clause, followed by the provided call statement, followed by
  /// an expect statement for every ensures clause.
  /// </summary>
  /// <param name="requires">The list of requires clause expressions.</param>
  /// <param name="ensures">The list of ensures clause expressions.</param>
  /// <param name="callStmt">The call statement to include.</param>
  /// <returns>The newly-created block statement.</returns>
  private static BlockStmt MakeContractCheckingBody(List<AttributedExpression> requires, List<AttributedExpression> ensures, Statement callStmt) {
    var expectRequiresStmts = requires.Select(req =>
      CreateContractExpectStatement(req, "requires"));
    var expectEnsuresStmts = ensures.Select(ens =>
      CreateContractExpectStatement(ens, "ensures"));
    var callStmtList = new List<Statement>() { callStmt };
    var bodyStatements = expectRequiresStmts.Concat(callStmtList).Concat(expectEnsuresStmts);
    return new BlockStmt(callStmt.Tok, callStmt.EndTok, bodyStatements.ToList());
  }

  private bool ShouldGenerateWrapper(MemberDecl decl) {
    // TODO: make this more discriminating
    // TODO: could work for ghost statements eventually
    return !decl.IsGhost && decl is not Constructor;
  }

  private void AddWrapper(TopLevelDeclWithMembers parent, MemberDecl decl) {
    var tok = decl.tok; // TODO: do better

    if (decl is Method origMethod) {
      var newMethod = cloner.CloneMethod(origMethod);
      newMethod.Name = origMethod.Name + "_checked";

      var args = newMethod.Ins.Select(Expression.CreateIdentExpr).ToList();
      var outs = newMethod.Outs.Select(Expression.CreateIdentExpr).ToList();
      var receiver = origMethod.IsStatic
        ? (Expression)new StaticReceiverExpr(tok, parent, false)
        : (Expression)new ThisExpr(parent);
      var selector = new MemberSelectExpr(tok, receiver, origMethod.Name) {
        Member = origMethod,
        TypeApplication_JustMember = new List<Type>(), // TODO: fill in properly
        TypeApplication_AtEnclosingClass = new List<Type>() // TODO: fill in properly
      };
      var callStmt = new CallStmt(tok, tok, outs, selector, args);

      var body = MakeContractCheckingBody(origMethod.Req, origMethod.Ens, callStmt);
      newMethod.Body = body;
      parent.Members.Add(newMethod);
    } else if (decl is Function origFunc) {
      var newFunc = cloner.CloneFunction(origFunc);
      newFunc.Name = origFunc.Name + "_checked";

      var args = origFunc.Formals.Select(Expression.CreateIdentExpr).ToList();
      var callExpr = new FunctionCallExpr(tok, origFunc.Name, new ThisExpr(tok), tok, tok, args);
      newFunc.Body = callExpr;
      var receiver = origFunc.IsStatic ?
        (Expression)new StaticReceiverExpr(tok, parent, false) :
        (Expression)new ThisExpr(parent);
      var selector = new MemberSelectExpr(tok, receiver, origFunc.Name) {
        Member = origFunc,
        TypeApplication_JustMember = new List<Type>(), // TODO: fill in properly
        TypeApplication_AtEnclosingClass = new List<Type>() // TODO: fill in properly
      };

      var localName = origFunc.Result?.Name ?? "__result";
      var local = new LocalVariable(tok, tok, localName, origFunc.ResultType, false);
      var localExpr = new IdentifierExpr(tok, localName);
      var callRhs = new ExprRhs(callExpr);

      var lhss = new List<Expression> { localExpr };
      var locs = new List<LocalVariable> { local };
      var rhss = new List<AssignmentRhs> { callRhs };

      var callStmt = origFunc.Result?.Name is null
        ? (Statement)new VarDeclStmt(tok, tok, locs, new UpdateStmt(tok, tok, lhss, rhss))
        : (Statement)new AssignStmt(tok, tok, localExpr, callRhs);

      var body = MakeContractCheckingBody(origFunc.Req, origFunc.Ens, callStmt);
      body.AppendStmt(new ReturnStmt(tok, tok, new List<AssignmentRhs> { new ExprRhs(localExpr) }));
      newFunc.ByMethodBody = body;
      parent.Members.Add(newFunc);
    }
  }

  internal override void PreResolve(ModuleDefinition moduleDefinition) {
    // Keep a list of members to wrap so that we don't modify the collection we're iterating over.
    List<(TopLevelDeclWithMembers, MemberDecl)> membersToWrap = new();

    foreach (var topLevelDecl in moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
      foreach (var decl in topLevelDecl.Members) {
        if (ShouldGenerateWrapper(decl)) {
          membersToWrap.Add((topLevelDecl, decl));
        }
      }
    }

    foreach (var (topLevelDecl, decl) in membersToWrap) {
      AddWrapper(topLevelDecl, decl);
    }
  }

  internal override void PostResolve(ModuleDefinition moduleDefinition) {
    // TODO: replace calls as dictated by the policy currently enabled
  }
}
