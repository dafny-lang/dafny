using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny; 

public class RunAllTestsMainMethod : IRewriter {

  private readonly List<Method> testMethods = new();
  private Method mainMethod;
  
  public RunAllTestsMainMethod(ErrorReporter reporter) : base(reporter) {
  }

  internal override void PreResolve(Program program) {
    var hasMain = Compilers.SinglePassCompiler.HasMain(program, out mainMethod);
    if (hasMain) {
      Reporter.Error(MessageSource.Rewriter, mainMethod.tok, "Cannot use /runAllTests on a program with a main method");
      return;
    }

    mainMethod = new Method(Token.NoToken, "Main", false, false,
      new List<TypeParameter>(), new List<Formal>(), new List<Formal>(),
      new List<AttributedExpression>(),
      new Specification<FrameExpression>(new List<FrameExpression>(), null),
      new List<AttributedExpression>(), new Specification<Expression>(new List<Expression>(), null),
      null, null, null);
    var defaultCompileModule = program.RawModules().Single(m => m.IsDefaultModule);
    var defaultClass = (DefaultClassDecl)defaultCompileModule.TopLevelDecls.Single(d => d is DefaultClassDecl);
    defaultClass.Members.Add(mainMethod);
  }

  internal override void PostResolve(ModuleDefinition moduleDefinition) {
    foreach(ICallable callable in ModuleDefinition.AllCallables(moduleDefinition.TopLevelDecls)) {
      if ((callable is Method method) && Attributes.Contains(method.Attributes, "test")) {
        testMethods.Add(method);
      }
    }
  }
  
  internal override void PostResolve(Program program) {
    var tok = Token.NoToken;
    List<Statement> mainMethodStatements = new();
    var idGenerator = new FreshIdGenerator();
    
    // var success := true;
    var successVarStmt = Statement.CreateLocalVariable(tok, "success", Expression.CreateBoolLiteral(tok, true));
    mainMethodStatements.Add(successVarStmt);
    var successVar = successVarStmt.Locals[0];
    var successVarExpr = new IdentifierExpr(tok, successVar);

    foreach(var method in testMethods) {
      // print "TestMethod: ";
      // try {
      //   var result := TestMethod();
      //   if result.IsFailure() {
      //     print "FAILED\n\t", result, "\n";
      //     success := false;
      //   } else {
      //     print "PASSED\n";
      //   }
      // } recover (haltMessage: string) {
      //   print "FAILED\n\t[Test Method Halted]", haltMessage, "\n";
      //   success := false;
      // }
      //
      // If the test method doesn't return a value, then the "try" block
      // will only contain the test method call and printing success.

      mainMethodStatements.Add(Statement.CreatePrintStmt(tok,
        Expression.CreateStringLiteral(tok, $"{method.FullDafnyName}: ")));

      var receiverExpr = new StaticReceiverExpr(tok, (TopLevelDeclWithMembers)method.EnclosingClass, true);
      var methodSelectExpr = new MemberSelectExpr(tok, receiverExpr, method.Name);
      methodSelectExpr.Member = method;
      methodSelectExpr.TypeApplication_JustMember = new List<Type>();
      methodSelectExpr.TypeApplication_AtEnclosingClass = new List<Type>();

      Expression resultVarExpr = null;
      var statements = new List<Statement>();
      var lhss = new List<Expression>();

      // If the method returns a value, check for a failure using IsFailure() as if this
      // was an AssignOrReturnStmt (:-).
      if (method.Outs.Count > 1) {
        Reporter.Error(MessageSource.Rewriter, method.tok,
          "Methods with the {:test} attribute can only have at most one return value");
        continue;
      }

      if (method.Outs.Count == 1) {
        var resultVarName = idGenerator.FreshId("result");
        var resultVarStmt = Statement.CreateLocalVariable(tok, resultVarName, method.Outs[0].Type);
        statements.Add(resultVarStmt);
        resultVarExpr = new IdentifierExpr(tok, resultVarStmt.Locals[0]);
        lhss.Add(resultVarExpr);
      }

      var callStmt = new CallStmt(tok, tok, lhss, methodSelectExpr, new List<Expression>());
      statements.Add(callStmt);

      Statement passedStmt = Statement.CreatePrintStmt(tok, Expression.CreateStringLiteral(tok, "PASSED\n"));
      var passedBlock = new BlockStmt(tok, tok, Util.Singleton(passedStmt));

      if (resultVarExpr != null) {
        var failureGuardExpr =
          new FunctionCallExpr(tok, "IsFailure", resultVarExpr, tok, new List<Expression>());
        var resultClass = (TopLevelDeclWithMembers)((UserDefinedType)resultVarExpr.Type).ResolvedClass;
        var isFailureMember = resultClass.Members.First(m => m.Name == "IsFailure");
        failureGuardExpr.Function = (Function)isFailureMember;
        var failedBlock = PrintTestFailureStatement(tok, successVarExpr, resultVarExpr);
        statements.Add(new IfStmt(tok, tok, false, failureGuardExpr, failedBlock, passedBlock));
      } else {
        statements.Add(passedBlock);
      }

      var runTestMethodBlock = new BlockStmt(tok, tok, statements);

      // Recovering from halting
      var haltMessageVarName = "haltMessage";
      var haltedBlock =
        PrintTestFailureStatement(tok, successVarExpr, new IdentifierExpr(tok, haltMessageVarName));
      var haltRecoveryStmt = new HaltRecoveryStatement(runTestMethodBlock, haltMessageVarName, haltedBlock);

      mainMethodStatements.Add(haltRecoveryStmt);
    }

    // For now just print a footer to call attention to any failed tests.
    // Ideally we would also set the process return code, but since Dafny main methods
    // don't support that yet, that is deferred for now.
    //
    // if !success {
    //   print "Test failures occurred: see above.\n";
    // }
    Statement printFailure = Statement.CreatePrintStmt(tok,
      Expression.CreateStringLiteral(tok, "Test failures occurred: see above.\n"));
    var failuresBlock = new BlockStmt(tok, tok, Util.Singleton(printFailure));
    var ifNotSuccess = new IfStmt(tok, tok, false, Expression.CreateNot(tok, successVarExpr), failuresBlock, null);
    mainMethodStatements.Add(ifNotSuccess);

    mainMethod.Body = new BlockStmt(tok, tok, mainMethodStatements);
  }

  private VarDeclStmt CreateLocalVariableStmt(IToken tok, string name, Type type) {
    var variable = new LocalVariable(tok, tok, name, type, false);
    variable.type = type;
    return new VarDeclStmt(tok, tok, Util.Singleton(variable), null);
  }
  
  private VarDeclStmt CreateLocalVariableStmt(IToken tok, string name, Expression value) {
    var variable = new LocalVariable(tok, tok, name, value.Type, false);
    variable.type = value.Type;
    Expression variableExpr = new IdentifierExpr(tok, name);
    var variableUpdateStmt = new UpdateStmt(tok, tok, Util.Singleton(variableExpr),
      Util.Singleton<AssignmentRhs>(new ExprRhs(value)));
    return new VarDeclStmt(tok, tok, Util.Singleton(variable), variableUpdateStmt);
  }
  
  private BlockStmt PrintTestFailureStatement(IToken tok, Expression successVarExpr, Expression failureValueExpr) {
    var failedPrintStmt = Statement.CreatePrintStmt(tok,
      Expression.CreateStringLiteral(tok, "FAILED\n\t"),
      failureValueExpr,
      Expression.CreateStringLiteral(tok, "\n"));
    var failSuiteStmt =
      new AssignStmt(tok, tok, successVarExpr, new ExprRhs(Expression.CreateBoolLiteral(tok, false)));
    return new BlockStmt(tok, tok, Util.List<Statement>(failedPrintStmt, failSuiteStmt));
  }
}