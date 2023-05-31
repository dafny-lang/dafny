#nullable disable

using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Language;
using Function = Microsoft.Dafny.Function;
using IdentifierExpr = Microsoft.Dafny.IdentifierExpr;
using IToken = Microsoft.Dafny.IToken;
using LetExpr = Microsoft.Dafny.LetExpr;
using LocalVariable = Microsoft.Dafny.LocalVariable;
using Program = Microsoft.Dafny.Program;
using Token = Microsoft.Dafny.Token;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.Inlining;

public class RemoveShortCircuitingRewriter : SyntaxTreeVisitor {

  public static readonly string TmpVarName = "#tmp";
  private List<(Statement original, List<Statement> substitution)> newStatements = new();

  public override void VisitUnknown(object node, IToken token) {
    return;
  }

  public override void Visit(Program program) {
    Visit(program.DefaultModule);
  }

  public override void Visit(TopLevelDecl d) {
    if (d is LiteralModuleDecl moduleDecl) {
      moduleDecl.ModuleDef.TopLevelDecls.ForEach(Visit);
    } else if (d is TopLevelDeclWithMembers withMembers) {
      withMembers.Members.OfType<Microsoft.Dafny.Function>().Iter(Visit);
      withMembers.Members.OfType<Method>().Iter(Visit);
    }
  }

  public override void Visit(Function function) {
    if (function.ByMethodBody != null) {
      RemoveShortCircuitingCloner.ResetVariableIds();
      Visit(function.ByMethodBody);
    }
  }

  public override void Visit(Method method) {
    RemoveShortCircuitingCloner.ResetVariableIds();
    if (method.Body != null) {
      Visit(method.Body);
    }
  }

  private void VisitNullableBlock(BlockStmt? blockStatement) {
    if (blockStatement != null) {
      Visit(blockStatement);
    }
  }

  private void VisitNullableExpression(Expression? expression) {
    if (expression != null) {
      Visit(expression);
    }
  }

  private void VisitNullableStatement(Statement? statement) {
    if (statement != null) {
      Visit(statement);
    }
  }

  // TODO
  public override void Visit(WhileStmt whileStatement) {
    Visit(whileStatement.Guard);
    VisitNullableBlock(whileStatement.Body);
  }

  // TODO
  public override void Visit(ForLoopStmt forStatement) {
    Visit(forStatement.Start);
    VisitNullableExpression(forStatement.End);
    VisitNullableBlock(forStatement.Body);
  }

  // TODO
  public override void Visit(AlternativeLoopStmt alternativeLoopStatement) {
    foreach (var guardedAlternative in alternativeLoopStatement.Alternatives) {
      Visit(guardedAlternative);
    }
  }

  // TODO
  public override void Visit(IfStmt ifStatement) {
    // A guard may be null when using an asterisk for non-deterministic choices.
    if (ifStatement.Guard != null) {
      var noCircuits = RemoveShortCircuit(ifStatement.Guard, false);
      ifStatement.Guard = noCircuits.expr;
      newStatements.Last().substitution.AddRange(noCircuits.stmts);
    }
    if (ifStatement.Thn != null) {
      Visit(ifStatement.Thn);
    }
    if (ifStatement.Els != null) {
      ifStatement.Els = ProcessStmtToStmt(ifStatement.Els);
    }
  }

  // TODO
  public override void Visit(AlternativeStmt alternativeStatement) {
    foreach (var guardedAlternative in alternativeStatement.Alternatives) {
      Visit(guardedAlternative);
    }
  }

  // TODO
  public override void Visit(GuardedAlternative guardedAlternative) {
    Visit(guardedAlternative.Guard);
    foreach (var statement in guardedAlternative.Body) {
      Visit(statement);
    }
  }

  // TODO
  public override void Visit(VarDeclStmt variableDeclarationStatement) {
    if (variableDeclarationStatement.Update != null) {
      Visit(variableDeclarationStatement.Update);
    }
  }

  // TODO
  public override void Visit(UpdateStmt updateStatement) {
    VisitRhss(updateStatement.Rhss, true);
  }

  private void VisitRhss(List<AssignmentRhs> rhss, bool insideUpdateStatement) {
    if (rhss == null) {
      return;
    }
    List<AssignmentRhs> newRhss = new();
    foreach (var rhs in rhss) {
      var noCircuits = RemoveShortCircuit((rhs as ExprRhs)?.Expr, insideUpdateStatement);
      if (noCircuits.stmts != null) {
        newStatements.Last().substitution.AddRange(noCircuits.stmts);
      }
      newRhss.Add(new ExprRhs(noCircuits.expr, rhs.Attributes));
    }
    rhss.Clear();
    rhss.AddRange(newRhss);
  }

  public override void Visit(AssertStmt assertStatement) { }

  // TODO: Assume statement

  public override void Visit(ReturnStmt returnStatement) {
    VisitRhss(returnStatement.Rhss, false);
  }

  // TODO
  public override void Visit(MatchStmt matchStatement) {
    Visit(matchStatement.Source);
    foreach (var matchCase in matchStatement.Cases) {
      Visit(matchCase);
    }
  }

  // TODO
  public override void Visit(MatchCaseStmt matchCaseStatement) {
    foreach (var argument in matchCaseStatement.Arguments) {
      Visit(argument);
    }

    foreach (var body in matchCaseStatement.Body) {
      Visit(body);
    }
  }

  // TODO
  public override void Visit(NestedMatchStmt nestedMatchStatement) {
    var noCircuits = RemoveShortCircuit(nestedMatchStatement.Source, false);
    nestedMatchStatement.Source = noCircuits.expr;
    newStatements.Last().substitution.AddRange(noCircuits.stmts);
    var newCases = new List<NestedMatchCaseStmt>();
    foreach (var nestedMatchCase in nestedMatchStatement.Cases) {
      newCases.Add(new NestedMatchCaseStmt(new RangeToken(new Token(), new Token()), nestedMatchCase.Pat, ProcessStmtList(nestedMatchCase.Body)));
    }
    nestedMatchStatement.Cases.Clear();
    nestedMatchStatement.Cases.AddRange(newCases);
  }

  public override void Visit(PrintStmt printStatement) {
    List<Expression> newArgs = new();
    foreach (var argument in printStatement.Args) {
      var noCircuits = RemoveShortCircuit(argument, false);
      if (noCircuits.stmts != null) {
        newStatements.Last().substitution.AddRange(noCircuits.stmts);
      }

      newArgs.Add(noCircuits.expr);
    }

    printStatement.Args.Clear();
    printStatement.Args.AddRange(newArgs);
  }

  public override void Visit(BlockStmt blockStatement) {
    int i = 0;
    while (blockStatement.Body.Count > i) {
      var newStatements = ProcessStmt(blockStatement.Body[i]);
      blockStatement.Body.RemoveAt(i);
      blockStatement.Body.InsertRange(i, newStatements);
      i += newStatements.Count;
    }
  }
  
  public Statement ProcessStmtToStmt(Statement statement) {
    var statements = ProcessStmt(statement);
    if (statements.Count == 1) {
      return statements[0];
    }
    return new BlockStmt(new RangeToken(new Token(), new Token()), statements);
  }

  public List<Statement> ProcessStmt(Statement statement) {
    var result = new List<Statement> { statement };
    newStatements.Add((statement, new List<Statement>()));
    Visit(statement);
    if (newStatements.Last().substitution.Count == 0) {
      newStatements.RemoveAt(newStatements.Count - 1);
      return result;
    }
    result.InsertRange(0, newStatements.Last().substitution);
    newStatements.RemoveAt(newStatements.Count - 1);
    return result;
  }
  
  public List<Statement> ProcessStmtList(List<Statement> statements) {
    var result = new List<Statement> {  };
    foreach (var statement in statements) {
      result.AddRange(ProcessStmt(statement));
    }
    return result;
  }

  public (List<Statement> stmts, Expression expr) RemoveShortCircuit(Expression expr, bool insideUpdateStatement) {
    var result = new RemoveShortCircuitingCloner().RemoveOneShortCircuit(expr, insideUpdateStatement);
    if (result.stmts.Count == 0) {
      return (result.stmts, result.expr);
    }

    var resultTmp = RemoveShortCircuit(result.expr, insideUpdateStatement);
    List<Statement> processed;
    if (resultTmp.stmts.Count != 0)  {
      result.stmts.AddRange(resultTmp.stmts);
    }

    var statements = ProcessStmtList(result.stmts);
    return (statements, resultTmp.expr);
  }

  private class RemoveShortCircuitingCloner : Cloner {

    private List<Statement> newStmts = new();
    private bool foundShortCircuit = false;
    private static int nextVariableId = 0;
    private bool insideUpdateStatement = true;

    public static void ResetVariableIds() {
      nextVariableId = 0;
    }
    private static string GetNewLocalVariableName() {
      return TmpVarName + nextVariableId++;
    }

    public (List<Statement> stmts, Expression expr) RemoveOneShortCircuit(Expression expr, bool insideUpdateStatement) {
      newStmts = new();
      foundShortCircuit = false;
      this.insideUpdateStatement = insideUpdateStatement;
      expr = CloneExpr(expr);
      return (newStmts, expr);
    }

    private RangeToken getRTok() {
      return new RangeToken(new Token(), new Token());
    }

    private Expression CreateIf(string tmpVarName, Type typ, Expression initialExpr, Expression testExpr,
      Expression thenExpr, Expression elseExpr) {
      var identifierExpr = new IdentifierExpr(new Token(), tmpVarName);
      var updateStmt = initialExpr != null
        ? new UpdateStmt(getRTok(), new List<Expression>() { identifierExpr },
          new List<AssignmentRhs>() { new ExprRhs(initialExpr) })
        : null;
      typ ??= new InferredTypeProxy();
      var varDecl = new VarDeclStmt(
          getRTok(),
          new List<LocalVariable>() { new(getRTok(), tmpVarName, typ, false) }, updateStmt);
      var thenStmt = new UpdateStmt(
        getRTok(),
        new List<Expression>() { identifierExpr },
        new List<AssignmentRhs>() { new ExprRhs(thenExpr) });
      var elseStmt = elseExpr != null
        ? new UpdateStmt(getRTok(), new List<Expression>() { identifierExpr },
          new List<AssignmentRhs>() { new ExprRhs(elseExpr) })
        : null;
      var ifStmt = new IfStmt(new RangeToken(new Token(), new Token()), false, testExpr,
        new BlockStmt(getRTok(), new List<Statement>() { thenStmt }), elseStmt);
      newStmts = new List<Statement>() { varDecl, ifStmt };
      return identifierExpr;
    }

    public override Expression CloneExpr(Expression expr) {
      // the newStmt should not be made into a block!!!
      // TODO: isGhost and isBindingGuard below are not clear
      var insideUpdateStatement = this.insideUpdateStatement;
      this.insideUpdateStatement = false;
      if (foundShortCircuit) {
        return base.CloneExpr(expr);
      }
      
      foundShortCircuit = true;
      var tmpVarName = GetNewLocalVariableName();
      var identifierExpr = new IdentifierExpr(new Token(), tmpVarName);
      VarDeclStmt varDecl = new VarDeclStmt(
        getRTok(),
        new List<LocalVariable>() { new(getRTok(), tmpVarName, new InferredTypeProxy(), false) }, null);
      BlockStmt blockUpdate = new BlockStmt(getRTok(), new List<Statement>());
      UpdateStmt updateStmt;
      int i = 0;
      
      switch (expr) {
        case ITEExpr iteExpr:
          return CreateIf(tmpVarName, iteExpr.Type, null, iteExpr.Test, iteExpr.Thn, iteExpr.Els);
        case BinaryExpr { Op: BinaryExpr.Opcode.And } binaryExpr:
          return CreateIf(tmpVarName, Type.Bool, binaryExpr.E0, identifierExpr, binaryExpr.E1, null);
        case BinaryExpr { Op: BinaryExpr.Opcode.Or } binaryExpr:
          return CreateIf(tmpVarName, Type.Bool, binaryExpr.E0,
            new UnaryOpExpr(new Token(), UnaryOpExpr.Opcode.Not, identifierExpr), binaryExpr.E1, null);
        case BinaryExpr { Op: BinaryExpr.Opcode.Imp } binaryExpr:
          return CreateIf(tmpVarName, Type.Bool, binaryExpr.E0, identifierExpr, binaryExpr.E1,
            new Microsoft.Dafny.LiteralExpr(new Token(), true));
        case BinaryExpr { Op: BinaryExpr.Opcode.Exp } binaryExpr:
          return CreateIf(tmpVarName, Type.Bool, binaryExpr.E1, identifierExpr, binaryExpr.E0,
            new Microsoft.Dafny.LiteralExpr(new Token(), true));
        case StmtExpr stmtExpr:
          newStmts.Add(varDecl);
          updateStmt = new UpdateStmt(getRTok(), new List<Expression>() { identifierExpr },
            new List<AssignmentRhs>() { new ExprRhs(stmtExpr.E) });
          blockUpdate.Body.Add(stmtExpr.S);
          blockUpdate.Body.Add(updateStmt);
          return identifierExpr;
        case NestedMatchExpr matchExpr:
          newStmts.Add(varDecl);
          var caseStmts = new List<NestedMatchCaseStmt>();
          foreach (var c in matchExpr.Cases) {
            updateStmt = new UpdateStmt(getRTok(), new List<Expression>() { identifierExpr },
              new List<AssignmentRhs>() { new ExprRhs(c.Body) });
            caseStmts.Add(new NestedMatchCaseStmt(getRTok(), c.Pat, new List<Statement>() {updateStmt}));
          }
          var matchStmt = new NestedMatchStmt(getRTok(), matchExpr.Source, caseStmts, false, matchExpr.Attributes);
          newStmts.Add(matchStmt);
          return identifierExpr;
        case LetExpr letExpr:
          if (letExpr.Exact == false || letExpr.BoundVars.Count() != letExpr.RHSs.Count) {
            // TODO
            foundShortCircuit = true;
            return base.CloneExpr(expr);
          }
          newStmts.Add(varDecl);
          i = 0;
          foreach (var boundVar in letExpr.BoundVars) {
            identifierExpr = new IdentifierExpr(new Token(), boundVar.Name);
            updateStmt = new UpdateStmt(getRTok(), new List<Expression>() { identifierExpr },
                new List<AssignmentRhs>() { new ExprRhs(letExpr.RHSs[i]) });
            varDecl = new VarDeclStmt(
              getRTok(),
              new List<LocalVariable>() { new(getRTok(), boundVar.Name, new InferredTypeProxy(), false) }, updateStmt);
            blockUpdate.Body.Add(varDecl);
            i += 1;
          }
          identifierExpr = new IdentifierExpr(new Token(), tmpVarName);
          updateStmt = new UpdateStmt(getRTok(), new List<Expression>() { identifierExpr },
            new List<AssignmentRhs>() { new ExprRhs(letExpr.Body) });
          blockUpdate.Body.Add(updateStmt);
          newStmts.Add(blockUpdate);
          return identifierExpr;
        case ApplySuffix applySuffix:
          if (insideUpdateStatement) {
            break;
          }
          updateStmt = new UpdateStmt(getRTok(), new List<Expression>() { identifierExpr },
            new List<AssignmentRhs>() { new ExprRhs(applySuffix) });
          newStmts.Add(varDecl);
          newStmts.Add(updateStmt);
          return identifierExpr;
        case ComprehensionExpr or MatchExpr:
          foundShortCircuit = true; // TODO
          return base.CloneExpr(expr);
      }
      nextVariableId--; // the new variable was not used in the end
      foundShortCircuit = false;
      return base.CloneExpr(expr);
    }
  }

}