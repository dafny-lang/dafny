using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
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
  private readonly SystemModuleManager systemModuleManager;

  public ExpectContracts(ErrorReporter reporter, SystemModuleManager systemModuleManager) : base(reporter) {
    this.systemModuleManager = systemModuleManager;
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
    var tok = expr.E.Origin;
    var msg = $"Runtime failure of {exprType} clause from {tok.OriginToString(Reporter.Options)}";
    var exprToCheck = expr.E;
    if (ExpressionTester.UsesSpecFeatures(exprToCheck)) {
      ReportWarning(ErrorId.rw_clause_cannot_be_compiled, tok,
        $"The {exprType} clause at this location cannot be compiled to be tested at runtime because it references ghost state.");
      exprToCheck = Expression.CreateBoolLiteral(tok, true);
      msg += " (not compiled because it references ghost state)";
    }
    var msgExpr = Expression.CreateStringLiteral(tok, msg);
    return new ExpectStmt(expr.E.Origin, exprToCheck, msgExpr, null);
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
    return new BlockStmt(callStmt.Origin, bodyStatements.ToList());
  }

  private bool ShouldGenerateWrapper(MemberDecl decl) {
    return !decl.IsGhost && CallRedirector.HasExternAttribute(decl);
  }

  /// <summary>
  /// Create a wrapper for the given function or method declaration that
  /// dynamically checks all of its preconditions, calls it, and checks
  /// all of its postconditions before returning. Then add the new wrapper
  /// as a sibling of the original declaration.
  /// </summary>
  /// <param name="parent">The declaration containing the on to be wrapped.</param>
  /// <param name="decl">The declaration to be wrapped.</param>
  private void GenerateWrapper(ModuleDefinition module, TopLevelDeclWithMembers parent, MemberDecl decl) {
    var tok = decl.Origin;

    var newName = decl.Name + "__dafny_checked";
    MemberDecl newDecl = null;

    if (decl is MethodOrConstructor origMethod) {
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
      module.CallRedirector.AddFullName(newDecl, decl.FullName + "__dafny_checked");
    }
  }

  private MemberDecl GenerateFunctionWrapper(TopLevelDeclWithMembers parent, MemberDecl decl, Function origFunc,
    string newName, IOrigin tok) {
    var newFunc = cloner.CloneFunction(origFunc);
    newFunc.NameNode.Value = newName;

    var args = newFunc.Ins.Select(Expression.CreateIdentExpr).ToList();
    var receiver = ModuleResolver.GetReceiver(parent, origFunc, decl.Origin);
    var callExpr = Expression.CreateResolvedCall(tok, receiver, origFunc, args,
      newFunc.TypeArgs.Select(tp => (Type)new UserDefinedType(tp)).ToList(), systemModuleManager);

    newFunc.Body = callExpr;

    var resultVar = origFunc.Result ?? new Formal(tok, "#result", newFunc.ResultType, false, false, null);
    var localExpr = Expression.CreateIdentExpr(resultVar);

    var callRhs = new ExprRhs(callExpr);
    var callStmt = new SingleAssignStmt(decl.Origin, localExpr, callRhs);

    var body = MakeContractCheckingBody(origFunc.Req, origFunc.Ens, callStmt);

    newFunc.ByMethodTok = Token.NoToken;
    newFunc.ByMethodBody = body;
    // We especially want to remove {:extern} from the wrapper, but also any other attributes.
    newFunc.Attributes = null;
    RegisterResolvedByMethod(resultVar, newFunc, parent);

    return newFunc;
  }

  private MemberDecl GenerateMethodWrapper(TopLevelDeclWithMembers parent, MemberDecl decl, MethodOrConstructor origMethod,
    string newName) {
    var newMethod = cloner.CloneMethod(origMethod);
    newMethod.NameNode.Value = newName;

    var args = newMethod.Ins.Select(Expression.CreateIdentExpr).ToList();
    var outs = newMethod.Outs.Select(Expression.CreateIdentExpr).ToList();
    var receiver = ModuleResolver.GetReceiver(parent, origMethod, decl.Origin);
    var memberSelectExpr = new MemberSelectExpr(decl.Origin, receiver, origMethod.NameNode);
    memberSelectExpr.Member = origMethod;
    memberSelectExpr.TypeApplicationJustMember =
      newMethod.TypeArgs.Select(tp => (Type)new UserDefinedType(tp)).ToList();
    memberSelectExpr.TypeApplicationAtEnclosingClass =
      parent.TypeArgs.Select(tp => (Type)new UserDefinedType(tp)).ToList();
    var callStmt = new CallStmt(decl.Origin, outs, memberSelectExpr, args);

    var body = MakeContractCheckingBody(origMethod.Req, origMethod.Ens, callStmt);
    newMethod.SetBody(body);
    return newMethod;
  }


  private void RegisterResolvedByMethod(Formal resultVar, Function f, TopLevelDeclWithMembers cl) {

    var tok = f.ByMethodTok;
    var r = Expression.CreateIdentExpr(resultVar);
    // To construct the receiver, we want to know if the function is static or instance. That information is ordinarily computed
    // by f.IsStatic, which looks at f.HasStaticKeyword and f.EnclosingClass. However, at this time, f.EnclosingClass hasn't yet
    // been set. Instead, we compute here directly from f.HasStaticKeyword and "cl".
    var isStatic = f.HasStaticKeyword || cl is DefaultClassDecl;
    var receiver = isStatic ? (Expression)new StaticReceiverExpr(tok, cl, true) : new ImplicitThisExpr(tok) {
      Type = UserDefinedType.FromTopLevelDecl(Token.NoToken, cl)
    };
    var fn = Expression.CreateResolvedCall(tok, receiver, f, f.Ins.ConvertAll(Expression.CreateIdentExpr),
      f.TypeArgs.ConvertAll(typeParameter => (Type)new UserDefinedType(f.Origin, typeParameter)), systemModuleManager);
    var post = new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Eq, r, fn) {
      Type = Type.Bool
    });
    // If f.Reads is empty, replace it with an explicit `reads {}` so that we don't replace that
    // with the default `reads *` for methods later.
    var reads = f.Reads;
    if (!reads.Expressions.Any()) {
      reads = new Specification<FrameExpression>();
      var emptySet = new SetDisplayExpr(tok, true, []);
      reads.Expressions.Add(new FrameExpression(tok, emptySet, null));
    }
    var method = new Method(f.Origin, f.NameNode, f.Attributes, f.HasStaticKeyword, false, f.TypeArgs,
        f.Ins, f.Req, [post], reads, f.Decreases, [resultVar],
        new Specification<FrameExpression>([], null), f.ByMethodBody, null, true);
    Contract.Assert(f.ByMethodDecl == null);
    method.InheritVisibility(f);
    method.FunctionFromWhichThisIsByMethodDecl = f;
    method.EnclosingClass = cl;
    f.ByMethodDecl = method;
  }

  /// <summary>
  /// Adds wrappers for certain top-level declarations in the given
  /// program and redirects callers to call those wrappers instead of
  /// the original members.
  ///
  /// This runs after resolution so that it has access to ghostness
  /// information, attributes and call targets and after verification
  /// because that makes the interaction with the refinement transformer
  /// more straightforward.
  /// </summary>
  /// <param name="program">The program to generate wrappers for and in.</param>
  public override void PostVerification(Program program) {
    // Create wrappers
    foreach (var moduleDefinition in program.Modules()) {

      // Keep a list of members to wrap so that we don't modify the collection we're iterating over.
      List<(TopLevelDeclWithMembers, MemberDecl)> membersToWrap = [];

      moduleDefinition.CallRedirector = new(Reporter);

      // Find module members to wrap.
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
        foreach (var decl in topLevelDecl.Members) {
          if (ShouldGenerateWrapper(decl)) {
            membersToWrap.Add((topLevelDecl, decl));
          }
        }
      }

      // Generate a wrapper for each of the members identified above. This
      // need to happen after all declarations to wrap have been identified
      // because it adds new declarations and would invalidate the iterator
      // used during identification.
      foreach (var (topLevelDecl, decl) in membersToWrap) {
        GenerateWrapper(moduleDefinition, topLevelDecl, decl);
      }
      moduleDefinition.CallRedirector.NewRedirections = wrappedDeclarations;

      // Put redirections in place. Any wrappers to call will be in either
      // this module or to a previously-processed module, so they'll already
      // exist.
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
        foreach (var decl in topLevelDecl.Members) {
          if (decl is ICallable callable) {
            moduleDefinition.CallRedirector?.Visit(callable, decl);
          }
        }
      }
    }

    if (Reporter.Options.TestContracts != DafnyOptions.ContractTestingMode.TestedExterns) {
      return;
    }

    foreach (var module in program.Modules()) {
      if (module.CallRedirector == null) {
        continue;
      }
      // If running in TestedExterns, warn if any extern has no corresponding test.
      var uncalledRedirections =
        module.CallRedirector.NewRedirections.ExceptBy(module.CallRedirector.CalledWrappers, x => x.Value);
      foreach (var uncalledRedirection in uncalledRedirections) {
        var uncalledOriginal = uncalledRedirection.Key;
        ReportWarning(ErrorId.rw_unreachable_by_test, uncalledOriginal.Origin, $"No :test code calls {uncalledOriginal.FullDafnyName}");
      }
    }

  }
}

/// <summary>
/// This class implements a top-down AST traversal to replace certain
/// function and method calls with calls to wrappers that dynamically
/// check contracts using expect statements.
/// </summary>
public class CallRedirector : TopDownVisitor<MemberDecl> {
  public Dictionary<MemberDecl, MemberDecl> NewRedirections { get; set; } = new();
  private readonly Dictionary<MemberDecl, string> newFullNames = new();
  private readonly ErrorReporter reporter;
  public HashSet<MemberDecl> CalledWrappers { get; } = [];

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
      reporter.Warning(MessageSource.Rewriter, ErrorId.rw_no_wrapper.ToString(), caller.Origin, $"Internal: no wrapper for {callee.FullDafnyName}");
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
        resolved.NameNode = newTarget.NameNode;
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
        resolved.MemberNameNode = newTarget.NameNode;
        CalledWrappers.Add(newTarget);
      }
    }

    return true;
  }
}
