using System.Collections.Generic;
using System.Linq;
using System.Threading;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging.Abstractions;

namespace DafnyCore.Backends;

public static class GhostEraser {
  class GhostCodeRemover : ASTVisitor<ICodeContext> {
    protected override bool VisitOneStatement(Statement stmt, ICodeContext context) {
      if (stmt is BlockStmt blockStmt) {
        var statements = blockStmt.Body;
        RemoveGhostStatements(statements);
      }

      if (stmt is AssignStatement assignStatement) {
        RemoveGhostStatements(assignStatement.ResolvedStatements);
      }
      return base.VisitOneStatement(stmt, context);
    }

    protected override bool VisitOneExpression(Expression expr, ICodeContext context) {
      if (expr is LetExpr letExpr) {
        letExpr.LHSs = letExpr.LHSs.Where(lhs => !lhs.Var.IsGhost).ToList();
      }
      return base.VisitOneExpression(expr, context);
    }

    protected override void VisitCasePattern<T>(CasePattern<T> pattern) {
      pattern.Arguments = pattern.Arguments.Where(lhs => !lhs.Var.IsGhost).ToList();
      base.VisitCasePattern(pattern);
    }

    private static void RemoveGhostStatements(List<Statement> statements)
    {
      for (int i = statements.Count - 1; i >= 0; i--) {
        if (statements[i].IsGhost) {
          statements.RemoveAt(i);
        }
      }
    }

    public override ICodeContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
      return (ICodeContext)astVisitorContext;
    }
  }

  public static void EraseGhostCode(Program program) {
    var symbolTable = SymbolTable.CreateFrom(NullLogger.Instance, program, CancellationToken.None);
    foreach (var compileModule in program.CompileModules) {
      foreach (var decl in compileModule.TopLevelDecls) {
        if (decl is DatatypeDecl datatypeDecl) {
          foreach (var constructor in datatypeDecl.Ctors) {                
            RemoveGhostParameters(program, symbolTable, constructor, constructor.Formals);
          }
        }
        if (decl is TopLevelDeclWithMembers withMembers) {
          withMembers.Members = withMembers.Members.Where(m => !m.IsGhost).ToList();
          foreach (var member in withMembers.Members) {
            switch (member)
            {
              case MethodOrFunction methodOrFunction: {
                if (Attributes.Contains(methodOrFunction.Attributes, "test")) {
                  program.Reporter.Error(MessageSource.Compiler, GeneratorErrors.ErrorId.c_test_function_must_be_compilable, methodOrFunction.tok,
                    $"Function {methodOrFunction.FullName} must be compiled to use the {{:test}} attribute");
                }
                
                RemoveGhostParameters(program, symbolTable, member, methodOrFunction.Ins);
                if (methodOrFunction is Method method) {
                  new GhostCodeRemover().VisitMethod(method);
                  // Remove ghost outs.
                }
                break;
              }
            }
          }
        }
      }
      
      foreach (var decl in compileModule.TopLevelDecls) {
        if (decl is TopLevelDeclWithMembers withMembers) {
          foreach (var member in withMembers.Members) {
            if (member is MethodOrFunction methodOrFunction) {
              methodOrFunction.Ins = methodOrFunction.Ins.Where(i => !i.IsGhost).ToList();
            } 
          }
        }
      }
    }
    
  }

  private static void RemoveGhostParameters(Program program, SymbolTable symbolTable, IHasNavigationToken member,
    List<Formal> formals)
  {
    var references = symbolTable.GetReferences(member);
    foreach (var reference in references) {
      if (reference is FunctionCallExpr functionCallExpr) {
        for (int i = functionCallExpr.Args.Count - 1; i >= 0; i--) {
          if (formals[i].IsGhost) {
            functionCallExpr.Args.RemoveAt(i);
          }
        }

      }
      if (reference is MemberSelectExpr memberSelectExpr) {
        var applySuffix = program.FindNode<ApplySuffix>(memberSelectExpr.Tok.Uri, memberSelectExpr.Tok.ToDafnyPosition());
        if (applySuffix != null) {
          if (applySuffix.Lhs == memberSelectExpr) {
            for (int i = applySuffix.Args.Count - 1; i >= 0; i--) {
              if (formals[i].IsGhost) {
                applySuffix.Args.RemoveAt(i);
              }
            }
          }
        }
      }
    }

    for (int i = formals.Count - 1; i >= 0; i--) {
      if (formals[i].IsGhost) {
        formals.RemoveAt(i);
      }
    }
  }
}