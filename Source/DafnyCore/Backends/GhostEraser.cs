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
      pattern.Arguments = pattern.Arguments?.Where(lhs => !lhs.Var.IsGhost).ToList();
      base.VisitCasePattern(pattern);
    }

    private static void RemoveGhostStatements(List<Statement> statements) {
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
      foreach (var topLevelDecl in compileModule.TopLevelDecls) {
        if (topLevelDecl is DatatypeDecl datatypeDecl) {
          foreach (var constructor in datatypeDecl.Ctors) {
            var removalLocations = RemoveGhostParameters(program, symbolTable, constructor, constructor.Formals);
            RemoveElementsAtGhostPositions(constructor.Destructors, removalLocations);
          }
        }
        if (topLevelDecl is TopLevelDeclWithMembers withMembers) {
          for (int i = withMembers.Members.Count - 1; i >= 0; i--) {
            var member = withMembers.Members[i];
            if (member.IsGhost) {
              if (member is Method && Attributes.Contains(member.Attributes, "test")) {
                program.Reporter.Error(MessageSource.Compiler, GeneratorErrors.ErrorId.c_test_function_must_be_compilable, member.Origin,
                  $"Function {member.FullName} must be compiled to use the {{:test}} attribute");
              }

              withMembers.Members.RemoveAt(i);
            }
          }

          foreach (var member in withMembers.Members) {
            switch (member) {
              case MethodOrFunction methodOrFunction: {

                  RemoveGhostParameters(program, symbolTable, member, methodOrFunction.Ins);
                  if (methodOrFunction is Function { ByMethodDecl: not null } function) {
                    new GhostCodeRemover().VisitMethod(function.ByMethodDecl);
                  }
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

  private static List<int> RemoveGhostParameters(Program program, SymbolTable symbolTable, IHasNavigationToken member,
    List<Formal> formals) {
    var removalLocations = new List<int>();
    for (var index = formals.Count - 1; index >= 0; index--) {
      var formal = formals[index];
      if (formal.IsGhost) {
        removalLocations.Add(index);
      }
    }

    for (int i = formals.Count - 1; i >= 0; i--) {
      if (formals[i].IsGhost) {
        formals.RemoveAt(i);
      }
    }

    RemoveGhostParameters(program, symbolTable, member, removalLocations);
    return removalLocations;
  }

  private static void RemoveGhostParameters(Program program, SymbolTable symbolTable, IHasNavigationToken member, List<int> removalLocations) {
    var references = symbolTable.GetReferences(member.NavigationToken);
    foreach (var reference in references) {
      if (reference is MatchCase matchCase) {
        RemoveElementsAtGhostPositions(matchCase.Arguments, removalLocations);
      }
      if (reference is IdPattern idPattern) {
        RemoveElementsAtGhostPositions(idPattern.Arguments, removalLocations);
      }
      if (reference is DatatypeValue datatypeValue) {
        RemoveElementsAtGhostPositions(datatypeValue.Arguments, removalLocations);
      }
      if (reference is FunctionCallExpr functionCallExpr) {
        RemoveElementsAtGhostPositions(functionCallExpr.Args, removalLocations);

      }
      if (reference is MemberSelectExpr memberSelectExpr) {
        var applySuffix = program.FindNode<ApplySuffix>(memberSelectExpr.Origin.Uri, memberSelectExpr.Origin.ToDafnyPosition());
        if (applySuffix != null) {
          if (applySuffix.Lhs == memberSelectExpr) {
            RemoveElementsAtGhostPositions(applySuffix.Args, removalLocations);
          }
        }
      }
    }

    return;

  }
  static void RemoveElementsAtGhostPositions<T>(List<T> list, List<int> removalLocations) {
    foreach (var index in removalLocations) {
      list.RemoveAt(index);
    }
  }
}