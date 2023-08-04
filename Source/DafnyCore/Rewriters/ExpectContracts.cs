using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Extensions.Logging.Abstractions;
using static Microsoft.Dafny.RewriterErrors;

namespace Microsoft.Dafny;

/// <summary>
/// This class implements a rewriter that will insert dynamic checks of
/// the contracts on certain functions and methods. It proceeds by
///
/// 1. identifying each declaration that should have its contract checked,
/// 2. creating a new wrapper definition that uses expect statements to
///    check all contract clauses for that declarations, and
/// 3. replacing calls to the original definition with calls to the new
///    wrapper definition.
/// </summary>
public class ExpectContracts : IRewriter {
  private readonly ClonerButDropMethodBodies cloner = new(true);
  private readonly Dictionary<MemberDecl, MemberDecl> wrappedDeclarations = new();
  private readonly CallRedirector callRedirector;

  public ExpectContracts(ErrorReporter reporter) : base(reporter) {
    callRedirector = new(reporter);
  }

  /// <summary>
  /// Create an expect statement that checks the given contract clause
  /// expression and fails with a message that points to the original
  /// location of the contract clause if it is not true at runtime.
  ///
  /// If the given clause is not compilable, emit a warning and construct
  /// an `expect true` statement with a message explaining the situation.
  /// </summary>
  /// <param name="expr">The contract clause expression to evaluate.</param>
  /// <param name="exprType">Either "requires" or "ensures", to use in the
  /// failure message.</param>
  /// <returns>The newly-created expect statement.</returns>
  private Statement CreateContractExpectStatement(AttributedExpression expr, string exprType) {
    var tok = expr.E.tok;
    var msg = $"Runtime failure of {exprType} clause from {tok.TokenToString(Reporter.Options)}";
    var exprToCheck = expr.E;
    if (ExpressionTester.UsesSpecFeatures(exprToCheck)) {
      ReportWarning(ErrorId.rw_clause_cannot_be_compiled, tok,
        $"The {exprType} clause at this location cannot be compiled to be tested at runtime because it references ghost state.");
      exprToCheck = new LiteralExpr(tok, true);
      exprToCheck.Type = Type.Bool;
      msg += " (not compiled because it references ghost state)";
    }
    var msgExpr = Expression.CreateStringLiteral(tok, msg);
    return new ExpectStmt(expr.E.RangeToken, exprToCheck, msgExpr, null);
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
  private BlockStmt MakeContractCheckingBody(IEnumerable<AttributedExpression> requires,
    IEnumerable<AttributedExpression> ensures, Statement callStmt) {
    var expectRequiresStmts = requires.Select(req =>
      CreateContractExpectStatement(req, "requires"));
    var expectEnsuresStmts = ensures.Select(ens =>
      CreateContractExpectStatement(ens, "ensures"));
    var callStmtList = new List<Statement>() { callStmt };
    var bodyStatements = expectRequiresStmts.Concat(callStmtList).Concat(expectEnsuresStmts);
    return new BlockStmt(callStmt.RangeToken, bodyStatements.ToList());
  }

  private bool ShouldGenerateWrapper(MemberDecl decl) {
    return !decl.IsGhost &&
           decl is not Constructor &&
           CallRedirector.HasExternAttribute(decl);
  }

  /// <summary>
  /// Create a wrapper for the given function or method declaration that
  /// dynamically checks all of its preconditions, calls it, and checks
  /// all of its postconditions before returning. Then add the new wrapper
  /// as a sibling of the original declaration.
  /// </summary>
  /// <param name="parent">The declaration containing the on to be wrapped.</param>
  /// <param name="decl">The declaration to be wrapped.</param>
  private void GenerateWrapper(TopLevelDeclWithMembers parent, MemberDecl decl) {
    var tok = decl.tok;

    var newName = decl.Name + "__dafny_checked";
    MemberDecl newDecl = null;

    if (decl is Method origMethod) {
      newDecl = GenerateMethodWrapper(parent, decl, origMethod, newName);
    } else if (decl is Function origFunc) {
      newDecl = GenerateFunctionWrapper(parent, decl, origFunc, newName, tok);
    }

    if (newDecl is not null) {
      // We especially want to remove {:extern} from the wrapper, but also any other attributes.
      newDecl.Attributes = null;

      newDecl.EnclosingClass = parent;
      wrappedDeclarations.Add(decl, newDecl);
      parent.Members.Add(newDecl);
      callRedirector.AddFullName(newDecl, decl.FullName + "__dafny_checked");
    }
  }

  private MemberDecl GenerateFunctionWrapper(TopLevelDeclWithMembers parent, MemberDecl decl, Function origFunc,
    string newName, IToken tok) {
    var newFunc = cloner.CloneFunction(origFunc);
    newFunc.NameNode.Value = newName;

    var args = newFunc.Formals.Select(Expression.CreateIdentExpr).ToList();
    var receiver = ModuleResolver.GetReceiver(parent, origFunc, decl.tok);
    var callExpr = new FunctionCallExpr(tok, origFunc.Name, receiver, null, null, args) {
      Function = origFunc,
      TypeApplication_JustFunction = newFunc.TypeArgs.Select(tp => (Type)new UserDefinedType(tp)).ToList(),
      TypeApplication_AtEnclosingClass = parent.TypeArgs.Select(tp => (Type)new UserDefinedType(tp)).ToList(),
      Type = newFunc.ResultType,
    };

    newFunc.Body = callExpr;

    var localName = origFunc.Result?.Name ?? "__result";
    var localExpr = new IdentifierExpr(tok, localName) {
      Type = newFunc.ResultType
    };

    var callRhs = new ExprRhs(callExpr);

    var lhss = new List<Expression> { localExpr };
    var rhss = new List<AssignmentRhs> { callRhs };

    var assignStmt = new AssignStmt(decl.RangeToken, localExpr, callRhs);
    Statement callStmt;
    if (origFunc.Result?.Name is null) {
      var local = new LocalVariable(decl.RangeToken, localName, newFunc.ResultType, false);
      local.type = newFunc.ResultType;
      var locs = new List<LocalVariable> { local };
      var varDeclStmt = new VarDeclStmt(decl.RangeToken, locs, new UpdateStmt(decl.RangeToken, lhss, rhss) {
        ResolvedStatements = new List<Statement>() { assignStmt }
      });
      localExpr.Var = local;
      callStmt = varDeclStmt;
    } else {
      localExpr.Var = origFunc.Result;
      callStmt = assignStmt;
    }

    var body = MakeContractCheckingBody(origFunc.Req, origFunc.Ens, callStmt);

    if (origFunc.Result?.Name is null) {
      body.AppendStmt(new ReturnStmt(decl.RangeToken, new List<AssignmentRhs> { new ExprRhs(localExpr) }));
    }

    newFunc.ByMethodBody = body;
    // We especially want to remove {:extern} from the wrapper, but also any other attributes.
    newFunc.Attributes = null;
    RegisterResolvedByMethod(newFunc, parent);

    return newFunc;
  }

  private MemberDecl GenerateMethodWrapper(TopLevelDeclWithMembers parent, MemberDecl decl, Method origMethod,
    string newName) {
    MemberDecl newDecl;
    var newMethod = cloner.CloneMethod(origMethod);
    newMethod.NameNode.Value = newName;

    var args = newMethod.Ins.Select(Expression.CreateIdentExpr).ToList();
    var outs = newMethod.Outs.Select(Expression.CreateIdentExpr).ToList();
    var receiver = ModuleResolver.GetReceiver(parent, origMethod, decl.tok);
    var memberSelectExpr = new MemberSelectExpr(decl.tok, receiver, origMethod.Name);
    memberSelectExpr.Member = origMethod;
    memberSelectExpr.TypeApplication_JustMember =
      newMethod.TypeArgs.Select(tp => (Type)new UserDefinedType(tp)).ToList();
    memberSelectExpr.TypeApplication_AtEnclosingClass =
      parent.TypeArgs.Select(tp => (Type)new UserDefinedType(tp)).ToList();
    var callStmt = new CallStmt(decl.RangeToken, outs, memberSelectExpr, args);

    var body = MakeContractCheckingBody(origMethod.Req, origMethod.Ens, callStmt);
    newMethod.Body = body;
    newDecl = newMethod;
    return newDecl;
  }


  private static void RegisterResolvedByMethod(Function f, TopLevelDeclWithMembers cl) {

    var tok = f.ByMethodTok;
    var resultVar = f.Result ?? new Formal(tok, "#result", f.ResultType, false, false, null);
    var r = Expression.CreateIdentExpr(resultVar);
    // To construct the receiver, we want to know if the function is static or instance. That information is ordinarily computed
    // by f.IsStatic, which looks at f.HasStaticKeyword and f.EnclosingClass. However, at this time, f.EnclosingClass hasn't yet
    // been set. Instead, we compute here directly from f.HasStaticKeyword and "cl".
    var isStatic = f.HasStaticKeyword || cl is DefaultClassDecl;
    var receiver = isStatic ? (Expression)new StaticReceiverExpr(tok, cl, true) : new ImplicitThisExpr(tok);
    var fn = new FunctionCallExpr(tok, f.Name, receiver, null, null,
      f.Formals.ConvertAll(Expression.CreateIdentExpr));
    var post = new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Eq, r, fn) {
      Type = Type.Bool
    });
    var method = new Method(f.RangeToken, f.NameNode, f.HasStaticKeyword, false, f.TypeArgs,
      f.Formals, new List<Formal>() { resultVar },
      f.Req, new Specification<FrameExpression>(new List<FrameExpression>(), null), new List<AttributedExpression>() { post }, f.Decreases,
      f.ByMethodBody, f.Attributes, null, true);
    Contract.Assert(f.ByMethodDecl == null);
    method.InheritVisibility(f);
    method.FunctionFromWhichThisIsByMethodDecl = f;
    method.EnclosingClass = cl;
    f.ByMethodDecl = method;
  }

  /// <summary>
  /// Add wrappers for certain top-level declarations in the given module.
  /// This runs after the first pass of resolution so that it has access to
  /// ghostness information, attributes and call targets.
  /// </summary>
  /// <param name="moduleDefinition">The module to generate wrappers for and in.</param>
  internal override void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
    // Keep a list of members to wrap so that we don't modify the collection we're iterating over.
    List<(TopLevelDeclWithMembers, MemberDecl)> membersToWrap = new();

    // Find module members to wrap.
    foreach (var topLevelDecl in moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
      foreach (var decl in topLevelDecl.Members) {
        if (ShouldGenerateWrapper(decl)) {
          membersToWrap.Add((topLevelDecl, decl));
        }
      }
    }

    // Generate a wrapper for each of the members identified above.
    foreach (var (topLevelDecl, decl) in membersToWrap) {
      GenerateWrapper(topLevelDecl, decl);
    }
    callRedirector.NewRedirections = wrappedDeclarations;
  }

  /// <summary>
  /// This class implements a top-down AST traversal to replace certain
  /// function and method calls with calls to wrappers that dynamically
  /// check contracts using expect statements.
  /// </summary>
  private class CallRedirector : TopDownVisitor<MemberDecl> {
    public Dictionary<MemberDecl, MemberDecl> NewRedirections { get; set; } = new();
    private readonly Dictionary<MemberDecl, string> newFullNames = new();
    private readonly ErrorReporter reporter;
    public HashSet<MemberDecl> CalledWrappers { get; } = new();

    public CallRedirector(ErrorReporter reporter) {
      this.reporter = reporter;
    }

    internal void AddFullName(MemberDecl decl, string fullName) {
      newFullNames.Add(decl, fullName);
    }

    internal static bool HasTestAttribute(MemberDecl decl) {
      return decl.Attributes is not null && Attributes.Contains(decl.Attributes, "test");
    }

    internal static bool HasExternAttribute(MemberDecl decl) {
      return decl.Attributes is not null && Attributes.Contains(decl.Attributes, "extern");
    }

    private bool ShouldCallWrapper(MemberDecl caller, MemberDecl callee) {
      if (!HasExternAttribute(callee)) {
        return false;
      }
      // If there's no wrapper for the callee, don't try to call it, but warn.
      if (!NewRedirections.ContainsKey(callee)) {
        reporter.Warning(MessageSource.Rewriter, ErrorId.rw_no_wrapper, caller.tok, $"Internal: no wrapper for {callee.FullDafnyName}");
        return false;
      }

      var opt = reporter.Options.TestContracts;
      return ((HasTestAttribute(caller) && opt == DafnyOptions.ContractTestingMode.TestedExterns) ||
              (opt == DafnyOptions.ContractTestingMode.Externs)) &&
             // Skip if the caller is a wrapper, otherwise it'd just call itself recursively.
             !NewRedirections.ContainsValue(caller);
    }

    protected override bool VisitOneExpr(Expression expr, ref MemberDecl decl) {
      if (expr is FunctionCallExpr fce) {
        var f = fce.Function;
        if (ShouldCallWrapper(decl, f)) {
          var newTarget = NewRedirections[f];
          var resolved = (FunctionCallExpr)fce.Resolved;
          resolved.Function = (Function)newTarget;
          resolved.Name = newTarget.Name;
          CalledWrappers.Add(newTarget);
        }
      }

      return true;
    }

    protected override bool VisitOneStmt(Statement stmt, ref MemberDecl decl) {
      if (stmt is CallStmt cs) {
        var m = cs.Method;
        if (ShouldCallWrapper(decl, m)) {
          var newTarget = NewRedirections[m];
          var resolved = (MemberSelectExpr)cs.MethodSelect.Resolved;
          resolved.Member = newTarget;
          resolved.MemberName = newTarget.Name;
          CalledWrappers.Add(newTarget);
        }
      }

      return true;
    }
  }

  public override void PostVerification(Program program) {
    foreach (var topLevelDecl in
             program.CompileModules.SelectMany(m => m.TopLevelDecls.OfType<TopLevelDeclWithMembers>())) {
      foreach (var decl in topLevelDecl.Members) {
        if (decl is ICallable callable) {
          callRedirector.Visit(callable, decl);
        }
      }
    }

    if (Reporter.Options.TestContracts != DafnyOptions.ContractTestingMode.TestedExterns) {
      return;
    }

    // If running in TestedExterns, warn if any extern has no corresponding test.
    var uncalledRedirections =
      callRedirector.NewRedirections.ExceptBy(callRedirector.CalledWrappers, x => x.Value);
    foreach (var uncalledRedirection in uncalledRedirections) {
      var uncalledOriginal = uncalledRedirection.Key;
      ReportWarning(ErrorId.rw_unreachable_by_test, uncalledOriginal.tok, $"No :test code calls {uncalledOriginal.FullDafnyName}");
    }
  }
}
