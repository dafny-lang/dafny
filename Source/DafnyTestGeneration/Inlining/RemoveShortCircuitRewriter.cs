// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Function = Microsoft.Dafny.Function;
using IdentifierExpr = Microsoft.Dafny.IdentifierExpr;
using LambdaExpr = Microsoft.Boogie.LambdaExpr;
using LetExpr = Microsoft.Dafny.LetExpr;
using LiteralExpr = Microsoft.Dafny.LiteralExpr;
using LocalVariable = Microsoft.Dafny.LocalVariable;
using Program = Microsoft.Dafny.Program;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.Inlining;

public class RemoveShortCircuitingRewriter : Cloner {

  // At any point during the AST traversal, newStmtStack.Last() contains the list of statements that must be inserted
  // before the currently processed expression/statement. E.g. when cloning the statement x := f1(f0(a)),
  // CloneStmt will return a new statement x := f1(#tmp0), and newStmtStack.Last() will be populated
  // with a statement #tmp0 := f0(a)
  private readonly List<List<Statement>> newStmtStack = new();
  // If foundShortCircuit==true, this class behaves exactly like a regular Cloner when processing expressions.
  // Must set this field to true before recursing on children of a short-circuiting expression that is being processed.
  private bool foundShortCircuit;
  public const string TmpVarPrefix = "#tmp"; // prefix to start the names of all newly created special variables
  private int nextVariableId; // the id to use when creating a new variable
  // If processingRhs==true, the parent of the currently processed AST node is UpdateStmt or AssignOrReturnStmt.
  // In the example above, f0(a) is not the right hand side of an update statement and so a special variable is created
  // to store the result of the function call, whereas f1(f0(a)) is a right hand side of an update statement and so
  // the result is stored in an already existing variable.
  private bool processingRhs;
  // determines whether short circuiting should be removed from method/function
  private readonly Func<MemberDecl, bool> shouldProcessPredicate;
  public RemoveShortCircuitingRewriter(Func<MemberDecl, bool> shouldProcessPredicate)
    : base(cloneLiteralModuleDefinition: false, cloneResolvedFields: false) {
    this.shouldProcessPredicate = shouldProcessPredicate;
  }

  private void ResetVariableIds() {
    nextVariableId = 0;
  }
  private string GetNewLocalVariableName() {
    return TmpVarPrefix + nextVariableId++;
  }

  public void PreResolve(Program program) {
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
    ResetVariableIds();
    if (function.ByMethodBody != null) {
      function.ByMethodBody = CloneBlockStmt(function.ByMethodBody);
    }
  }

  private void Visit(Method method) {
    ResetVariableIds();
    if (method.Body != null) {
      method.Body = CloneBlockStmt(method.Body);
    }
  }

  public override BlockStmt CloneBlockStmt(BlockStmt blockStatement) {
    if (blockStatement == null) {
      return null;
    }
    if (blockStatement is DividedBlockStmt dividedBlockStmt) {
      return CloneDividedBlockStmt(dividedBlockStmt);
    }
    List<Statement> newBody = new();
    foreach (var statement in blockStatement.Body) {
      newBody.AddRange(ProcessStmt(statement));
    }
    return new BlockStmt(blockStatement.Origin, newBody);
  }

  public override DividedBlockStmt CloneDividedBlockStmt(DividedBlockStmt blockStatement) {
    List<Statement> newBodyInit = new();
    List<Statement> newBodyProper = new();
    foreach (var statement in blockStatement.BodyInit) {
      var processed = ProcessStmt(statement);
      newBodyInit.AddRange(processed);
    }
    foreach (var statement in blockStatement.BodyProper) {
      var processed = ProcessStmt(statement);
      newBodyProper.AddRange(processed);
    }
    return new DividedBlockStmt(blockStatement.Origin, newBodyInit, blockStatement.SeparatorTok, newBodyProper);
  }

  private List<Statement> ProcessStmt(Statement statement) {
    newStmtStack.Add(new List<Statement>());
    var newStatement = CloneStmt(statement, false);
    var result = new List<Statement> { newStatement };
    if (newStmtStack.Last().Count == 0) {
      newStmtStack.RemoveAt(newStmtStack.Count - 1);
      return result;
    }
    result.InsertRange(0, newStmtStack.Last());
    newStmtStack.RemoveAt(newStmtStack.Count - 1);
    return result;
  }

  public override Statement CloneStmt(Statement statement, bool isReference) {
    if (statement == null) {
      return null;
    }
    switch (statement) {
      case IfStmt ifStatement:
        return CloneIfStmt(ifStatement);
      case AssignStatement updateStatement:
        return CloneUpdateStmt(updateStatement);
      case ReturnStmt returnStatement:
        return CloneReturnStmt(returnStatement);
      case BlockStmt blockStatement:
        return CloneBlockStmt(blockStatement);
      case NestedMatchStmt nestedMatchStatement:
        return CloneNestedMatchStmt(nestedMatchStatement);
      case PrintStmt printStatement:
        return ClonePrintStmt(printStatement);
      case WhileStmt whileStmt:
        return CloneWhileStmt(whileStmt);
      case AssignOrReturnStmt assignOrReturnStmt:
        return CloneAssignOrReturnStmt(assignOrReturnStmt);
      case ForLoopStmt forLoopStmt:
        return CloneForLoopStmt(forLoopStmt);
      case CallStmt callStmt:
        return CloneCallStmt(callStmt);
      case PredicateStmt or ForallStmt or HideRevealStmt: // always ghost?
        return statement;
      default:
        return base.CloneStmt(statement, isReference);
    }
  }

  private List<AssignmentRhs> CloneRhss(List<AssignmentRhs> rhss, bool processingRhs) {
    if (rhss == null) {
      return null;
    }
    List<AssignmentRhs> newRhss = new();
    foreach (var rhs in rhss) {
      if (rhs is TypeRhs) {
        newRhss.Add(rhs);
        continue;
      }
      var noCircuits = RemoveShortCircuit((rhs as ExprRhs)?.Expr, processingRhs);
      if (noCircuits.stmts != null) {
        newStmtStack.Last().AddRange(noCircuits.stmts);
      }
      newRhss.Add(new ExprRhs(noCircuits.expr, rhs.Attributes));
    }
    return newRhss;
  }

  private List<Expression> CloneExpressionList(List<Expression> expressions) {
    if (expressions == null) {
      return null;
    }
    List<Expression> newExpressions = new();
    foreach (var expression in expressions) {
      var noCircuits = RemoveShortCircuit(expression, true);
      if (noCircuits.stmts != null) {
        newStmtStack.Last().AddRange(noCircuits.stmts);
      }
      newExpressions.Add(noCircuits.expr);
    }
    return newExpressions;
  }

  private Statement CloneIfStmt(IfStmt ifStatement) {
    // A guard may be null when using an asterisk for non-deterministic choices.
    Expression guard = null;
    BlockStmt thn = null;
    Statement els = null;
    if (ifStatement.Guard != null) {
      var noCircuits = RemoveShortCircuit(ifStatement.Guard, false);
      guard = noCircuits.expr;
      newStmtStack.Last().AddRange(noCircuits.stmts);
    }
    if (ifStatement.Thn != null) {
      thn = CloneBlockStmt(ifStatement.Thn);
    }
    if (ifStatement.Els != null) {
      els = ProcessStmtToStmt(ifStatement.Els);
    }
    return new IfStmt(ifStatement.Origin, ifStatement.IsBindingGuard, guard, thn, els, ifStatement.Attributes);
  }

  private Statement CloneUpdateStmt(AssignStatement updateStatement) {
    return new AssignStatement(updateStatement.Origin, CloneExpressionList(updateStatement.Lhss), CloneRhss(updateStatement.Rhss, true));
  }

  private Statement CloneAssignOrReturnStmt(AssignOrReturnStmt assignOrReturnStmt) {
    ExprRhs rhs = null;
    if (assignOrReturnStmt.Rhs != null) {
      var noCircuits = RemoveShortCircuit(assignOrReturnStmt.Rhs.Expr, true);
      if (noCircuits.stmts != null) {
        newStmtStack.Last().AddRange(noCircuits.stmts);
      }
      rhs = new ExprRhs(noCircuits.expr, assignOrReturnStmt.Rhs.Attributes);
    }
    return new AssignOrReturnStmt(assignOrReturnStmt.Origin, CloneExpressionList(assignOrReturnStmt.Lhss), rhs,
      assignOrReturnStmt.KeywordToken, CloneRhss(assignOrReturnStmt.Rhss, true));
  }

  private Statement CloneReturnStmt(ReturnStmt returnStatement) {
    return new ReturnStmt(returnStatement.Origin, CloneRhss(returnStatement.Rhss, false));
  }

  private Statement CloneCallStmt(CallStmt callStmt) {
    return new CallStmt(callStmt.Origin, CloneExpressionList(callStmt.Lhs), callStmt.MethodSelect, CloneExpressionList(callStmt.Args));
  }

  private Statement CloneNestedMatchStmt(NestedMatchStmt nestedMatchStatement) {
    var noCircuits = RemoveShortCircuit(nestedMatchStatement.Source, false);
    newStmtStack.Last().AddRange(noCircuits.stmts);
    var newCases = new List<NestedMatchCaseStmt>();
    foreach (var nestedMatchCase in nestedMatchStatement.Cases) {
      newCases.Add(new NestedMatchCaseStmt(nestedMatchCase.Origin, nestedMatchCase.Pat, ProcessStmtList(nestedMatchCase.Body)));
    }
    return new NestedMatchStmt(nestedMatchStatement.Origin, noCircuits.expr, newCases, nestedMatchStatement.UsesOptionalBraces, nestedMatchStatement.Attributes);
  }

  private Statement ClonePrintStmt(PrintStmt printStatement) {
    return new PrintStmt(printStatement.Origin, CloneExpressionList(printStatement.Args));
  }

  private Statement CloneWhileStmt(WhileStmt whileStmt) {
    var noCircuits = RemoveShortCircuit(whileStmt.Guard, false);
    newStmtStack.Last().AddRange(noCircuits.stmts);
    var newBody = CloneBlockStmt(whileStmt.Body);
    newBody.Body.AddRange(ProcessStmtList(noCircuits.stmts.Where(stmt => stmt is not VarDeclStmt).ToList()));
    return new WhileStmt(whileStmt.Origin, noCircuits.expr, whileStmt.Invariants, whileStmt.Decreases, whileStmt.Mod, newBody);
  }

  private Statement CloneForLoopStmt(ForLoopStmt forLoopStmt) {
    var start = RemoveShortCircuit(forLoopStmt.Start, false);
    newStmtStack.Last().AddRange(start.stmts);
    var end = RemoveShortCircuit(forLoopStmt.End, false);
    newStmtStack.Last().AddRange(end.stmts);
    var newBody = CloneBlockStmt(forLoopStmt.Body);
    return new ForLoopStmt(forLoopStmt.Origin, forLoopStmt.LoopIndex, start.expr, end.expr, forLoopStmt.GoingUp,
      forLoopStmt.Invariants, forLoopStmt.Decreases, forLoopStmt.Mod, newBody, forLoopStmt.Attributes);
  }

  private Statement ProcessStmtToStmt(Statement statement) {
    var statements = ProcessStmt(statement);
    if (statements.Count == 1) {
      return statements[0];
    }
    return new BlockStmt(statement.Origin, statements);
  }

  private List<Statement> ProcessStmtList(List<Statement> statements) {
    var result = new List<Statement>();
    foreach (var statement in statements) {
      result.AddRange(ProcessStmt(statement));
    }
    return result;
  }

  private (List<Statement> stmts, Expression expr) RemoveShortCircuit(Expression expr, bool processingRhs) {
    var newStmts = new List<Statement>();
    newStmtStack.Add(new List<Statement>());
    this.processingRhs = processingRhs;
    var result = RemoveOneShortCircuit(expr);
    newStmts.AddRange(newStmtStack.Last());
    newStmtStack.RemoveAt(newStmtStack.Count - 1);
    if (newStmts.Count == 0) {
      return (newStmts, result);
    }

    var resultTmp = RemoveShortCircuit(result, processingRhs);
    newStmts.AddRange(resultTmp.stmts);

    var statements = ProcessStmtList(newStmts);
    return (statements, resultTmp.expr);
  }

  private Expression RemoveOneShortCircuit(Expression expr) {
    foundShortCircuit = false;
    var newExpr = CloneExpr(expr);
    return newExpr;
  }

  private Expression CreateIf(string tmpVarName, Type typ, Expression initialExpr, Expression testExpr,
    Expression thenExpr, Expression elseExpr, Expression original) {
    var thenToken = thenExpr.StartToken.WithVal("#thenBranch");
    var elseToken = elseExpr.StartToken.WithVal("#elseBranch");
    var identifierExpr = new IdentifierExpr(original.StartToken, tmpVarName);
    typ ??= new InferredTypeProxy();
    var varDecl = new VarDeclStmt(
        new SourceOrigin(original.StartToken, original.StartToken),
        new List<LocalVariable> { new(new SourceOrigin(original.StartToken, original.StartToken), tmpVarName, typ, false) }, null);
    newStmtStack.Last().Add(varDecl);
    if (initialExpr != null) {
      var updateStmt = new AssignStatement(new SourceOrigin(original.StartToken, original.StartToken), new List<Expression> { identifierExpr },
          new List<AssignmentRhs> { new ExprRhs(initialExpr) });
      newStmtStack.Last().Add(updateStmt);
    }
    var thenStmt = new AssignStatement(
      thenToken,
      new List<Expression> { identifierExpr },
      new List<AssignmentRhs> { new ExprRhs(thenExpr) });
    var elseStmt = elseExpr != null
      ? new AssignStatement(elseToken, new List<Expression> { identifierExpr },
        new List<AssignmentRhs> { new ExprRhs(elseExpr) })
      : null;
    var ifStmt = new IfStmt(original.StartToken, false, testExpr,
      new BlockStmt(thenStmt.Origin, new List<Statement> { thenStmt }), elseStmt);
    newStmtStack.Last().Add(ifStmt);
    return identifierExpr;
  }

  public override Expression CloneExpr(Expression expr) {
    if (expr == null) {
      return null;
    }
    if (foundShortCircuit) {
      return base.CloneExpr(expr);
    }
    var wasProcessingRhs = processingRhs;
    processingRhs = false;

    foundShortCircuit = true;
    var tmpVarName = GetNewLocalVariableName();
    var identifierExpr = new IdentifierExpr(expr.StartToken, tmpVarName);
    VarDeclStmt varDecl = new VarDeclStmt(
      new SourceOrigin(expr.StartToken, expr.StartToken),
      new List<LocalVariable> { new(new SourceOrigin(expr.StartToken, expr.StartToken), tmpVarName, new InferredTypeProxy(), false) }, null);
    AssignStatement assignStatement;
    int i = 0;

    switch (expr) {
      case ITEExpr iteExpr:
        return CreateIf(tmpVarName, iteExpr.Type, null, iteExpr.Test, iteExpr.Thn, iteExpr.Els, iteExpr);
      case BinaryExpr { Op: BinaryExpr.Opcode.And } binaryExpr:
        return CreateIf(tmpVarName, Type.Bool, binaryExpr.E0, identifierExpr, binaryExpr.E1, new IdentifierExpr(binaryExpr.E0.EndToken, tmpVarName), binaryExpr);
      case BinaryExpr { Op: BinaryExpr.Opcode.Or } binaryExpr:
        return CreateIf(tmpVarName, Type.Bool, binaryExpr.E0,
          new UnaryOpExpr(binaryExpr.E0.StartToken, UnaryOpExpr.Opcode.Not, identifierExpr), binaryExpr.E1, new IdentifierExpr(binaryExpr.E0.EndToken, tmpVarName), binaryExpr);
      case BinaryExpr { Op: BinaryExpr.Opcode.Imp } binaryExpr:
        return CreateIf(tmpVarName, Type.Bool, binaryExpr.E0, identifierExpr, binaryExpr.E1,
          Expression.CreateBoolLiteral(binaryExpr.E0.EndToken, true), binaryExpr);
      case BinaryExpr { Op: BinaryExpr.Opcode.Exp } binaryExpr:
        return CreateIf(tmpVarName, Type.Bool, binaryExpr.E1, identifierExpr, binaryExpr.E0,
          Expression.CreateBoolLiteral(binaryExpr.E1.EndToken, true), binaryExpr);
      case StmtExpr stmtExpr:
        newStmtStack.Last().Add(varDecl);
        assignStatement = new AssignStatement(stmtExpr.E.Origin, new List<Expression> { identifierExpr },
          new List<AssignmentRhs> { new ExprRhs(stmtExpr.E) });
        var stmtBlockUpdate = new BlockStmt(new SourceOrigin(stmtExpr.S.StartToken, stmtExpr.E.EndToken), new List<Statement>());
        stmtBlockUpdate.Body.Add(stmtExpr.S);
        stmtBlockUpdate.Body.Add(assignStatement);
        newStmtStack.Last().Add(stmtBlockUpdate);
        return identifierExpr;
      case NestedMatchExpr matchExpr:
        newStmtStack.Last().Add(varDecl);
        var caseStmts = new List<NestedMatchCaseStmt>();
        foreach (var c in matchExpr.Cases) {
          assignStatement = new AssignStatement(new SourceOrigin(c.Body.StartToken, c.Body.StartToken), new List<Expression> { identifierExpr },
            new List<AssignmentRhs> { new ExprRhs(c.Body) });
          caseStmts.Add(new NestedMatchCaseStmt(new SourceOrigin(c.StartToken, c.StartToken), c.Pat, new List<Statement> { assignStatement }));
        }
        var matchStmt = new NestedMatchStmt(matchExpr.Origin, matchExpr.Source, caseStmts, false, matchExpr.Attributes);
        newStmtStack.Last().Add(matchStmt);
        return identifierExpr;
      case LetOrFailExpr { Lhs: not null } letOrFailExpr:
        newStmtStack.Last().Add(varDecl);
        var boundIdentifierExpr = new IdentifierExpr(letOrFailExpr.Rhs.StartToken, letOrFailExpr.Lhs.Var.Name);
        var assignOrReturn = new AssignOrReturnStmt(letOrFailExpr.Rhs.Origin, new List<Expression> { boundIdentifierExpr }, new ExprRhs(letOrFailExpr.Rhs), null, new List<AssignmentRhs>());
        varDecl = new VarDeclStmt(
          new SourceOrigin(letOrFailExpr.Lhs.Var.StartToken, letOrFailExpr.Rhs.EndToken),
          new List<LocalVariable> { new(letOrFailExpr.Lhs.Var.Origin, letOrFailExpr.Lhs.Var.Name, new InferredTypeProxy(), false) }, assignOrReturn);
        assignStatement = new AssignStatement(letOrFailExpr.Body.Origin, new List<Expression> { identifierExpr },
          new List<AssignmentRhs> { new ExprRhs(letOrFailExpr.Body) });
        newStmtStack.Last().Add(new BlockStmt(letOrFailExpr.Origin, new List<Statement> { varDecl, assignStatement }));
        return identifierExpr;
      case LetOrFailExpr letOrFailExpr:
        newStmtStack.Last().Add(varDecl);
        var assignOrReturnNoLhs = new AssignOrReturnStmt(letOrFailExpr.Rhs.Origin, new List<Expression>(), new ExprRhs(letOrFailExpr.Rhs), null, new List<AssignmentRhs>());
        assignStatement = new AssignStatement(letOrFailExpr.Body.Origin, new List<Expression> { identifierExpr },
          new List<AssignmentRhs> { new ExprRhs(letOrFailExpr.Body) });
        newStmtStack.Last().Add(new BlockStmt(letOrFailExpr.Origin, new List<Statement> { assignOrReturnNoLhs, assignStatement }));
        return identifierExpr;
      case LetExpr letExpr:
        if (letExpr.Exact == false || letExpr.BoundVars.Count() != letExpr.RHSs.Count) {
          return base.CloneExpr(expr);
        }
        newStmtStack.Last().Add(varDecl);
        i = 0;
        var blockUpdate = new BlockStmt(letExpr.Origin, new List<Statement>());
        foreach (var boundVar in letExpr.BoundVars) {
          identifierExpr = new IdentifierExpr(letExpr.RHSs[i].StartToken, boundVar.Name);
          assignStatement = new AssignStatement(letExpr.RHSs[i].Origin, new List<Expression> { identifierExpr },
              new List<AssignmentRhs> { new ExprRhs(letExpr.RHSs[i]) });
          varDecl = new VarDeclStmt(
            new SourceOrigin(boundVar.StartToken, letExpr.RHSs[i].EndToken),
            new List<LocalVariable> { new(boundVar.Origin, boundVar.Name, new InferredTypeProxy(), false) }, assignStatement);
          blockUpdate.Body.Add(varDecl);
          i += 1;
        }
        identifierExpr = new IdentifierExpr(letExpr.Body.StartToken, tmpVarName);
        assignStatement = new AssignStatement(letExpr.Body.Origin, new List<Expression> { identifierExpr },
          new List<AssignmentRhs> { new ExprRhs(letExpr.Body) });
        blockUpdate.Body.Add(assignStatement);
        newStmtStack.Last().Add(blockUpdate);
        return identifierExpr;
      case ApplySuffix applySuffix:
        if (wasProcessingRhs) {
          break;
        }
        assignStatement = new AssignStatement(applySuffix.Origin, new List<Expression> { identifierExpr },
          new List<AssignmentRhs> { new ExprRhs(applySuffix) });
        newStmtStack.Last().Add(varDecl);
        newStmtStack.Last().Add(assignStatement);
        return identifierExpr;
    }
    nextVariableId--; // the new variable was not used in the end
    foundShortCircuit = false;
    if (expr is SetComprehension or Microsoft.Dafny.LambdaExpr) {
      return expr;
    }
    return base.CloneExpr(expr);
  }


}