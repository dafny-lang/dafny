using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny; 

public class RunAllTestsMainMethod : IRewriter {

  public RunAllTestsMainMethod(ErrorReporter reporter) : base(reporter) {
  }

  /// <summary>
  /// Verifies that there isn't already a main method, and then creates
  /// one with no body (to be filled in by PostResolve()).
  ///
  /// It might be possible to move this to PostResolve() if we created a resolved
  /// Method instead, but for now this is a bit easier. It also allows us to produce
  /// errors much earlier in the pipeline.
  /// </summary>
  internal override void PreResolve(Program program) {
    Method mainMethod;
    var hasMain = Compilers.SinglePassCompiler.HasMain(program, out mainMethod);
    if (hasMain) {
      Reporter.Error(MessageSource.Rewriter, mainMethod.tok, "Cannot use /runAllTests on a program with a main method");
      return;
    }

    // Verifying the method isn't yet possible since the translation of try/recover statments is not implemented,
    // and would be low-value anyway.
    var noVerifyAttribute = new Attributes("verify", new List<Expression> { new LiteralExpr(RangeToken.NoToken, false) }, null);

    mainMethod = new Method(RangeToken.NoToken, "Main", false, false,
      new List<TypeParameter>(), new List<Formal>(), new List<Formal>(),
      new List<AttributedExpression>(),
      new Specification<FrameExpression>(new List<FrameExpression>(), null),
      new List<AttributedExpression>(), new Specification<Expression>(new List<Expression>(), null),
      null, noVerifyAttribute, null);
    var defaultModule = program.RawModules().Single(m => m.IsDefaultModule);
    var defaultClass = (DefaultClassDecl)defaultModule.TopLevelDecls.Single(d => d is DefaultClassDecl);
    defaultClass.Members.Add(mainMethod);
  }

  /// <summary>
  /// Generates the main method body that invokes every {:test} method and prints
  /// out the results.
  ///
  /// Note that this needs to be post-resolving so we can determine if each test method
  /// has a return value we need to check for IsFailure(). That means all the AST nodes
  /// we create need to be already fully-resolved.
  ///
  /// Example output:
  ///
  /// var success := true;
  /// 
  /// print "SomeModule.TestMethod1: ";
  /// try {
  ///   var result := SomeModule.TestMethod1();
  ///   if result.IsFailure() {
  ///     print "FAILED\n\t", result, "\n";
  ///     success := false;
  ///   } else {
  ///     print "PASSED\n";
  ///   }
  /// } recover (haltMessage: string) {
  ///   print "FAILED\n\t", haltMessage, "\n";
  ///   success := false;
  /// }
  /// 
  /// print "SomeOtherModule.TestMethod2NoResultValue: ";
  /// try {
  ///   SomeOtherModule.TestMethod2NoResultValue();
  ///   print "PASSED\n";
  /// } recover (haltMessage: string) {
  ///   print "FAILED\n\t", haltMessage, "\n";
  ///   success := false;
  /// }
  /// 
  /// ...
  ///
  /// if !success {
  ///   print "Test failures occurred: see above.\n";
  /// }
  /// </summary>
  internal override void PostResolve(Program program) {
    var tok2 = program.GetFirstTopLevelToken();
    var tok = new RangeToken(tok2, tok2);
    List<Statement> mainMethodStatements = new();
    var idGenerator = new FreshIdGenerator();

    // var success := true;
    var successVarStmt = Statement.CreateLocalVariable(tok, "success", Expression.CreateBoolLiteral(tok, true));
    mainMethodStatements.Add(successVarStmt);
    var successVar = successVarStmt.Locals[0];
    var successVarExpr = new IdentifierExpr(tok, successVar);

    foreach (var moduleDefinition in program.CompileModules) {
      foreach (var callable in ModuleDefinition.AllCallables(moduleDefinition.TopLevelDecls)) {
        if ((callable is Method method) && Attributes.Contains(method.Attributes, "test")) {
          // print "TestMethod: ";
          mainMethodStatements.Add(Statement.CreatePrintStmt(tok,
            Expression.CreateStringLiteral(tok, $"{method.FullDafnyName}: ")));

          // If the test method returns a value:
          //
          // var result := TestMethod();
          // if result.IsFailure() {
          //   print "FAILED\n\t", result, "\n";
          //   success := false;
          // } else {
          //   print "PASSED\n";
          // }
          //
          // Otherwise, just:
          //
          // TestMethod();
          // print "PASSED\n";
          var tryBodyStatements = new List<Statement>();

          var receiverExpr = new StaticReceiverExpr(tok, (TopLevelDeclWithMembers)method.EnclosingClass, true);
          var methodSelectExpr = new MemberSelectExpr(tok, receiverExpr, method.Name) {
            Member = method,
            TypeApplication_JustMember = new List<Type>(),
            TypeApplication_AtEnclosingClass = new List<Type>()
          };

          Expression resultVarExpr = null;
          var lhss = new List<Expression>();

          // If the method returns a value, check for a failure using IsFailure() as if this
          // was an AssignOrReturnStmt (:-).
          switch (method.Outs.Count) {
            case > 1:
              Reporter.Error(MessageSource.Rewriter, method.tok,
                "Methods with the {:test} attribute can have at most one return value");
              continue;
            case 1: {
                var resultVarName = idGenerator.FreshId("result");
                var resultVarStmt = Statement.CreateLocalVariable(tok, resultVarName, method.Outs[0].Type);
                tryBodyStatements.Add(resultVarStmt);
                resultVarExpr = new IdentifierExpr(tok, resultVarStmt.Locals[0]);
                resultVarExpr.Type = resultVarStmt.Locals[0].Type;
                lhss.Add(resultVarExpr);
                break;
              }
          }

          var callStmt = new CallStmt(tok, lhss, methodSelectExpr, new List<Expression>());
          tryBodyStatements.Add(callStmt);

          Statement passedStmt = Statement.CreatePrintStmt(tok, Expression.CreateStringLiteral(tok, "PASSED\n"));
          var passedBlock = new BlockStmt(tok, Util.Singleton(passedStmt));

          if (resultVarExpr != null) {
            var failureGuardExpr =
              new FunctionCallExpr(tok, "IsFailure", resultVarExpr, tok.StartToken, tok.EndToken, new List<Expression>());
            var resultClass = (TopLevelDeclWithMembers)((UserDefinedType)resultVarExpr.Type).ResolvedClass;
            var isFailureMember = resultClass.Members.First(m => m.Name == "IsFailure");
            failureGuardExpr.Function = (Function)isFailureMember;
            failureGuardExpr.Type = Type.Bool;
            failureGuardExpr.TypeApplication_JustFunction = new List<Type>();
            failureGuardExpr.TypeApplication_AtEnclosingClass = new List<Type>();

            var failedBlock = PrintTestFailureStatement(tok, successVarExpr, resultVarExpr);
            tryBodyStatements.Add(new IfStmt(tok, false, failureGuardExpr, failedBlock, passedBlock));
          } else {
            tryBodyStatements.Add(passedBlock);
          }

          var tryBody = new BlockStmt(tok, tryBodyStatements);

          // Wrap the code above with:
          //
          // try {
          //   ...
          // } recover (haltMessage: string) {
          //   print "FAILED\n\t", haltMessage, "\n";
          //   success := false;
          // }
          //
          var haltMessageVar = new LocalVariable(tok, "haltMessage", Type.String(), false) {
            type = Type.String()
          };
          var haltMessageVarExpr = new IdentifierExpr(tok, haltMessageVar);
          var recoverBlock =
            PrintTestFailureStatement(tok, successVarExpr, haltMessageVarExpr);
          var tryRecoverStmt = new TryRecoverStatement(tryBody, haltMessageVar, recoverBlock);

          mainMethodStatements.Add(tryRecoverStmt);
        }
      }
    }

    // Use an expect statement to halt if there are any failed tests.
    // Ideally we would just set the process return code instead of crashing the program,
    // but since Dafny main methods don't support that yet, that is deferred for now.
    //
    // expect success, "Test failures occurred: see above.\n";
    // 
    Statement expectSuccess = new ExpectStmt(tok, successVarExpr,
      Expression.CreateStringLiteral(tok, "Test failures occurred: see above.\n"), null);
    mainMethodStatements.Add(expectSuccess);

    // Find the resolved main method to attach the body to (which will be a different instance
    // than the Method we added in PreResolve).
    var hasMain = Compilers.SinglePassCompiler.HasMain(program, out var mainMethod);
    Contract.Assert(hasMain);
    mainMethod.Body = new BlockStmt(tok, mainMethodStatements);
  }

  private BlockStmt PrintTestFailureStatement(RangeToken tok, Expression successVarExpr, Expression failureValueExpr) {
    var failedPrintStmt = Statement.CreatePrintStmt(tok,
      Expression.CreateStringLiteral(tok, "FAILED\n\t"),
      failureValueExpr,
      Expression.CreateStringLiteral(tok, "\n"));
    var failSuiteStmt =
      new AssignStmt(tok, successVarExpr, new ExprRhs(tok, Expression.CreateBoolLiteral(tok, false)));
    return new BlockStmt(tok, Util.List<Statement>(failedPrintStmt, failSuiteStmt));
  }
}