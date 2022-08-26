using System;
using System.Collections.Generic;
using System.Data;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Microsoft.Dafny;

public class ExpectContracts : IRewriter {
  private readonly ClonerButDropMethodBodies cloner = new();
  private readonly Dictionary<string, (MemberDecl, MemberDecl)> wrappedDeclarations = new();
  private CallRedirector callRedirector;

  public ExpectContracts(ErrorReporter reporter) : base(reporter) { }

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
  private static BlockStmt MakeContractCheckingBody(List<AttributedExpression> requires,
    List<AttributedExpression> ensures, Statement callStmt) {
    var expectRequiresStmts = requires.Select(req =>
      CreateContractExpectStatement(req, "requires"));
    var expectEnsuresStmts = ensures.Select(ens =>
      CreateContractExpectStatement(ens, "ensures"));
    var callStmtList = new List<Statement>() { callStmt };
    var bodyStatements = expectRequiresStmts.Concat(callStmtList).Concat(expectEnsuresStmts);
    return new BlockStmt(callStmt.Tok, callStmt.EndTok, bodyStatements.ToList());
  }

  private static Expression MakeApplySuffix(IToken tok, string name, List<Expression> args) {
    var nameExpr = new NameSegment(tok, name, null);
    var argBindings = args.ConvertAll(arg => new ActualBinding(null, arg));
    return new ApplySuffix(tok, null, nameExpr, argBindings, tok);
  }

  private bool ShouldGenerateWrapper(MemberDecl decl) {
    // TODO: make this more discriminating
    // TODO: could work for ghost statements eventually
    return !decl.IsGhost && decl is not Constructor;
  }

  private void GenerateWrapper(TopLevelDeclWithMembers parent, MemberDecl decl) {
    var tok = decl.tok; // TODO: do better

    var newName = decl.Name + "_checked";
    MemberDecl newDecl = null;

    if (decl is Method origMethod) {
      var newMethod = cloner.CloneMethod(origMethod);
      newMethod.Name = newName;

      var args = newMethod.Ins.Select(Expression.CreateIdentExpr).ToList();
      var outs = newMethod.Outs.Select(Expression.CreateIdentExpr).ToList();
      var applyExpr = MakeApplySuffix(tok, origMethod.Name, args);
      var applyRhs = new ExprRhs(applyExpr);
      var callStmt = new UpdateStmt(tok, tok, outs, new List<AssignmentRhs>() { applyRhs });

      var body = MakeContractCheckingBody(origMethod.Req, origMethod.Ens, callStmt);
      newMethod.Body = body;
      newDecl = newMethod;
    } else if (decl is Function origFunc) {
      var newFunc = cloner.CloneFunction(origFunc);
      newFunc.Name = newName;

      var args = origFunc.Formals.Select(Expression.CreateIdentExpr).ToList();
      var callExpr = MakeApplySuffix(tok, origFunc.Name, args);
      newFunc.Body = callExpr;

      var localName = origFunc.Result?.Name ?? "__result";
      var local = new LocalVariable(tok, tok, localName, origFunc.ResultType, false);
      var localExpr = new IdentifierExpr(tok, localName);
      var callRhs = new ExprRhs(callExpr);

      var lhss = new List<Expression> { localExpr };
      var locs = new List<LocalVariable> { local };
      var rhss = new List<AssignmentRhs> { callRhs };

      var callStmt = origFunc.Result?.Name is null
        ? (Statement)new VarDeclStmt(tok, tok, locs, new UpdateStmt(tok, tok, lhss, rhss))
        : (Statement)new UpdateStmt(tok, tok, lhss, rhss);

      var body = MakeContractCheckingBody(origFunc.Req, origFunc.Ens, callStmt);

      if (origFunc.Result?.Name is null) {
        body.AppendStmt(new ReturnStmt(tok, tok, new List<AssignmentRhs> { new ExprRhs(localExpr) }));
      }
      newFunc.ByMethodBody = body;
      newDecl = newFunc;
    }

    if (newDecl is not null) {
      wrappedDeclarations.Add(decl.Name, (decl, newDecl));
    }
  }

  internal override void PreResolve(Program program) {

    // Keep a list of members to wrap so that we don't modify the collection we're iterating over.
    List<(TopLevelDeclWithMembers, MemberDecl)> membersToWrap = new();

    // Find module members to wrap
    foreach (var moduleDefinition in program.RawModules()) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
        foreach (var decl in topLevelDecl.Members) {
          if (ShouldGenerateWrapper(decl)) {
            membersToWrap.Add((topLevelDecl, decl));
          }
        }
      }
    }

    // Generate a wrapper for each of the members identified above
    foreach (var (topLevelDecl, decl) in membersToWrap) {
      GenerateWrapper(topLevelDecl, decl);
    }

    // Add the generated wrappers to the module
    foreach (var (topLevelDecl, decl) in membersToWrap) {
      if (wrappedDeclarations.ContainsKey(decl.Name)) {
        topLevelDecl.Members.Add(wrappedDeclarations[decl.Name].Item2);
      }
    }

    callRedirector = new CallRedirector(wrappedDeclarations);
  }

  class CallRedirector : TopDownVisitor<MemberDecl> {
    private readonly Dictionary<string, (MemberDecl, MemberDecl)> wrappedDeclarations;

    public CallRedirector(Dictionary<string, (MemberDecl, MemberDecl)> wrappedDeclarations) {
      this.wrappedDeclarations = wrappedDeclarations;
    }

    private bool HasTestAttribute(MemberDecl decl) {
      return decl.Attributes is not null && Attributes.Contains(decl.Attributes, "test");
    }

    private bool HasExternAttribute(MemberDecl decl) {
      return decl.Attributes is not null && Attributes.Contains(decl.Attributes, "extern");
    }

    private bool ShouldCallWrapper(MemberDecl caller, string calleeName) {
      if (!wrappedDeclarations.ContainsKey(calleeName)) {
        return false;
      }

      var callee = wrappedDeclarations[calleeName].Item2;
      // TODO: make this configurable
      return (HasTestAttribute(caller) || HasExternAttribute(callee)) &&
             // TODO: check this in a better way
             !caller.Name.EndsWith("_checked");
    }

    protected override bool VisitOneExpr(Expression expr, ref MemberDecl decl) {
      // TODO: this pulls targets from the original module. Fix that.
      if (expr is FunctionCallExpr fce) {
        Console.WriteLine($"Function call to {fce.Function.Name}");
        if (ShouldCallWrapper(decl, fce.Function.Name)) {
          var targetName = fce.Function.Name;
          var newTarget = wrappedDeclarations[targetName].Item2;
          Console.WriteLine($"Call (expression) to {targetName} redirecting to {newTarget.Name}");
          fce.Function = (Function)newTarget;
          fce.Name = newTarget.Name;
          var resolved = (FunctionCallExpr)fce.Resolved;
          resolved.Function = (Function)newTarget;
          resolved.Name = newTarget.Name;
        }
      }

      return true;
    }

    protected override bool VisitOneStmt(Statement stmt, ref MemberDecl decl) {
      // TODO: this pulls targets from the original module. Fix that.
      if (stmt is CallStmt cs) {
        Console.WriteLine($"Method call to {cs.Method.Name}");
        if (ShouldCallWrapper(decl, cs.Method.Name)) {
          var targetName = cs.Method.Name;
          var newTarget = wrappedDeclarations[targetName].Item2;
          Console.WriteLine($"Call (statement) to {targetName} redirecting to {newTarget.Name}");
          cs.MethodSelect.Member = newTarget;
          cs.MethodSelect.MemberName = newTarget.Name;
          var resolved = (MemberSelectExpr)cs.MethodSelect.Resolved;
          resolved.Member = newTarget;
          resolved.MemberName = newTarget.Name;
        }
      }

      return true;
    }
  }

  internal override void PostCompileCloneAndResolve(ModuleDefinition moduleDefinition) {
    foreach (var topLevelDecl in moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
      // TODO: keep track of names
      foreach (var decl in topLevelDecl.Members) { }
    }

    foreach (var topLevelDecl in moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
      foreach (var decl in topLevelDecl.Members) {
        if (decl is ICallable callable) {
          Console.WriteLine($"Visiting {decl.Name}");
          callRedirector.Visit(callable, decl);
        }
      }
    }
  }
}
