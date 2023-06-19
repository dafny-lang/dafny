#nullable disable

using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Function = Microsoft.Dafny.Function;
using IdentifierExpr = Microsoft.Dafny.IdentifierExpr;
using LetExpr = Microsoft.Dafny.LetExpr;
using LocalVariable = Microsoft.Dafny.LocalVariable;
using Program = Microsoft.Dafny.Program;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.Inlining;

public class RemoveShortCircuitingCloner : Cloner {

  public static readonly string TmpVarName = "#tmp";
  private List<List<Statement>> newStatements = new();
  private List<Statement> newStmts = new();
  private bool foundShortCircuit = false;
  private int nextVariableId = 0;
  private bool insideUpdateStatement = true;

  public void Visit(Program program) {
    Visit(program.DefaultModule);
  }

  private void Visit(TopLevelDecl d) {
    if (d is LiteralModuleDecl moduleDecl) {
      moduleDecl.ModuleDef.TopLevelDecls.Iter(Visit);
    } else if (d is TopLevelDeclWithMembers withMembers) {
      withMembers.Members.OfType<Microsoft.Dafny.Function>().Iter(Visit);
      withMembers.Members.OfType<Method>().Iter(Visit);
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
    if (method.Body != null && method.Name != "_ctor") { // TODO constructors!
      method.Body = CloneBlockStmt(method.Body);
    }
  }
  
  private List<AssignmentRhs> CloneRhss(List<AssignmentRhs> rhss, bool insideUpdateStatement) {
    if (rhss == null) {
      return null;
    }
    List<AssignmentRhs> newRhss = new();
    foreach (var rhs in rhss) {
      if (rhs is TypeRhs) {
        newRhss.Add(rhs);
        continue;
      }
      var noCircuits = RemoveShortCircuit((rhs as ExprRhs)?.Expr, insideUpdateStatement);
      if (noCircuits.stmts != null) {
        newStatements.Last().AddRange(noCircuits.stmts);
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
        newStatements.Last().AddRange(noCircuits.stmts);
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
      newStatements.Last().AddRange(noCircuits.stmts);
    }
    if (ifStatement.Thn != null) {
      thn = CloneBlockStmt(ifStatement.Thn);
    }
    if (ifStatement.Els != null) {
      els = ProcessStmtToStmt(ifStatement.Els);
    }
    return new IfStmt(ifStatement.RangeToken, ifStatement.IsBindingGuard, guard, thn, els, ifStatement.Attributes);
  }

  private Statement CloneUpdateStmt(UpdateStmt updateStatement) {
    return new UpdateStmt(updateStatement.RangeToken, CloneExpressionList(updateStatement.Lhss), CloneRhss(updateStatement.Rhss, true));
  }
  
  private Statement CloneAssignOrReturnStmt(AssignOrReturnStmt assignOrReturnStmt) {
    ExprRhs rhs = null;
    if (assignOrReturnStmt.Rhs != null) {
      var noCircuits = RemoveShortCircuit(assignOrReturnStmt.Rhs.Expr, insideUpdateStatement);
      if (noCircuits.stmts != null) {
        newStatements.Last().AddRange(noCircuits.stmts);
      }
      rhs = new ExprRhs(noCircuits.expr, assignOrReturnStmt.Rhs.Attributes);
    }
    return new AssignOrReturnStmt(assignOrReturnStmt.RangeToken, CloneExpressionList(assignOrReturnStmt.Lhss), rhs,
      assignOrReturnStmt.KeywordToken, CloneRhss(assignOrReturnStmt.Rhss, true));
  }

  private Statement CloneReturnStmt(ReturnStmt returnStatement) {
    return new ReturnStmt(returnStatement.RangeToken, CloneRhss(returnStatement.Rhss, false));
  }
  
  private Statement CloneNestedMatchStmt(NestedMatchStmt nestedMatchStatement) {
    var noCircuits = RemoveShortCircuit(nestedMatchStatement.Source, false);
    newStatements.Last().AddRange(noCircuits.stmts);
    var newCases = new List<NestedMatchCaseStmt>();
    foreach (var nestedMatchCase in nestedMatchStatement.Cases) {
      newCases.Add(new NestedMatchCaseStmt(nestedMatchCase.RangeToken, nestedMatchCase.Pat, ProcessStmtList(nestedMatchCase.Body)));
    }
    return new NestedMatchStmt(nestedMatchStatement.RangeToken, noCircuits.expr, newCases, nestedMatchStatement.UsesOptionalBraces, nestedMatchStatement.Attributes);
  }

  private Statement ClonePrintStmt(PrintStmt printStatement) {
    List<Expression> newArgs = new();
    foreach (var argument in printStatement.Args) {
      var noCircuits = RemoveShortCircuit(argument, false);
      if (noCircuits.stmts != null) {
        newStatements.Last().AddRange(noCircuits.stmts);
      }

      newArgs.Add(noCircuits.expr);
    }

    printStatement.Args.Clear();
    printStatement.Args.AddRange(newArgs);
    return printStatement;
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
    return new BlockStmt(blockStatement.RangeToken, newBody);
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
    return new DividedBlockStmt(blockStatement.RangeToken, newBodyInit, blockStatement.SeparatorTok, newBodyProper);
  }

  private Statement CloneWhileStmt(WhileStmt whileStmt) {
    var noCircuits = RemoveShortCircuit(whileStmt.Guard, false);
    newStatements.Last().AddRange(noCircuits.stmts);
    var newBody = CloneBlockStmt(whileStmt.Body);
    newBody.Body.AddRange(ProcessStmtList(noCircuits.stmts.Where(stmt => stmt is not VarDeclStmt).ToList()));
    // TODO: Clone invariants/decreases/modifies?
    return new WhileStmt(whileStmt.RangeToken, noCircuits.expr, whileStmt.Invariants, whileStmt.Decreases, whileStmt.Mod, newBody);
  }
  
  public override Statement CloneStmt(Statement statement) {
    if (statement == null) {
      return null;
    }
    switch (statement) {
      case IfStmt ifStatement:
        return CloneIfStmt(ifStatement);
      case UpdateStmt updateStatement:
        return CloneUpdateStmt(updateStatement);
      case ReturnStmt returnStatement:
        return CloneReturnStmt(returnStatement);
      case BlockStmt blockStatement:
        return CloneBlockStmt(blockStatement);
      case NestedMatchStmt nestedMatchStatement:
        return CloneNestedMatchStmt(nestedMatchStatement);
      case PrintStmt printStatement:
        return ClonePrintStmt(printStatement);
      case AssertStmt or AssumeStmt or ForallStmt or RevealStmt: // ghost and hence not modified
        return statement;
      case WhileStmt whileStmt:
        return CloneWhileStmt(whileStmt);
      case AssignOrReturnStmt assignOrReturnStmt:
        return CloneAssignOrReturnStmt(assignOrReturnStmt);
      default:
        return base.CloneStmt(statement); // TODO
    }
  }

  private Statement ProcessStmtToStmt(Statement statement) {
    var statements = ProcessStmt(statement);
    if (statements.Count == 1) {
      return statements[0];
    }
    return new BlockStmt(statement.RangeToken, statements);
  }

  private List<Statement> ProcessStmt(Statement statement) {
    newStatements.Add(new List<Statement>());
    var newStatement = CloneStmt(statement);
    var result = new List<Statement> { newStatement };
    if (newStatements.Last().Count == 0) {
      newStatements.RemoveAt(newStatements.Count - 1);
      return result;
    }
    result.InsertRange(0, newStatements.Last());
    newStatements.RemoveAt(newStatements.Count - 1);
    return result;
  }

  private List<Statement> ProcessStmtList(List<Statement> statements) {
    var result = new List<Statement> {  };
    foreach (var statement in statements) {
      result.AddRange(ProcessStmt(statement));
    }
    return result;
  }

  private (List<Statement> stmts, Expression expr) RemoveShortCircuit(Expression expr, bool insideUpdateStatement) {
    var result = RemoveOneShortCircuit(expr, insideUpdateStatement);
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

  private void ResetVariableIds() {
    nextVariableId = 0;
  }
  private string GetNewLocalVariableName() {
    return TmpVarName + nextVariableId++;
  }

  private (List<Statement> stmts, Expression expr) RemoveOneShortCircuit(Expression expr, bool insideUpdateStatement) {
    newStmts = new();
    foundShortCircuit = false;
    this.insideUpdateStatement = insideUpdateStatement;
    var newExpr = CloneExpr(expr);
    return (newStmts, newExpr);
  }

  private Expression CreateIf(string tmpVarName, Type typ, Expression initialExpr, Expression testExpr,
    Expression thenExpr, Expression elseExpr, Expression original) {
    var identifierExpr = new IdentifierExpr(original.StartToken, tmpVarName);
    typ ??= new InferredTypeProxy();
    var varDecl = new VarDeclStmt(
        new RangeToken(original.StartToken, original.StartToken),
        new List<LocalVariable>() { new(new RangeToken(original.StartToken, original.StartToken), tmpVarName, typ, false) }, null);
    newStmts = new List<Statement>() { varDecl };
    if (initialExpr != null) {
      var updateStmt = new UpdateStmt(new RangeToken(original.StartToken, original.StartToken), new List<Expression>() { identifierExpr },
          new List<AssignmentRhs>() { new ExprRhs(initialExpr) });
      newStmts.Add(updateStmt);
    }
    var thenStmt = new UpdateStmt(
      new RangeToken(thenExpr.StartToken, thenExpr.StartToken),
      new List<Expression>() { identifierExpr },
      new List<AssignmentRhs>() { new ExprRhs(thenExpr) });
    var elseStmt = elseExpr != null
      ? new UpdateStmt(new RangeToken(elseExpr.StartToken, elseExpr.StartToken), new List<Expression>() { identifierExpr },
        new List<AssignmentRhs>() { new ExprRhs(elseExpr) })
      : null; /*new UpdateStmt(new RangeToken(original.EndToken, original.EndToken), new List<Expression>() { identifierExpr },
        new List<AssignmentRhs>() { new ExprRhs(identifierExpr) }); // so that else branch gets its own test*/
    var ifStmt = new IfStmt(original.RangeToken, false, testExpr,
      new BlockStmt(thenExpr.RangeToken, new List<Statement>() { thenStmt }), elseStmt);
    newStmts.Add(ifStmt);
    return identifierExpr;
  }

  public override Expression CloneExpr(Expression expr) {
    // the newStmt should not be made into a block!!!
    // TODO: isGhost and isBindingGuard below are not clear
    if (expr == null) {
      return null;
    }
    var insideUpdateStatement = this.insideUpdateStatement;
    this.insideUpdateStatement = false;
    if (foundShortCircuit) {
      return base.CloneExpr(expr);
    }
    
    foundShortCircuit = true;
    var tmpVarName = GetNewLocalVariableName();
    var identifierExpr = new IdentifierExpr(expr.StartToken, tmpVarName);
    VarDeclStmt varDecl = new VarDeclStmt(
      new RangeToken(expr.StartToken, expr.StartToken),
      new List<LocalVariable>() { new(new RangeToken(expr.StartToken, expr.StartToken), tmpVarName, new InferredTypeProxy(), false) }, null);
    UpdateStmt updateStmt;
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
          new Microsoft.Dafny.LiteralExpr(binaryExpr.E0.EndToken, true), binaryExpr);
      case BinaryExpr { Op: BinaryExpr.Opcode.Exp } binaryExpr:
        return CreateIf(tmpVarName, Type.Bool, binaryExpr.E1, identifierExpr, binaryExpr.E0,
          new Microsoft.Dafny.LiteralExpr(binaryExpr.E1.EndToken, true), binaryExpr);
      case StmtExpr stmtExpr:
        newStmts.Add(varDecl);
        updateStmt = new UpdateStmt(stmtExpr.E.RangeToken, new List<Expression>() { identifierExpr },
          new List<AssignmentRhs>() { new ExprRhs(stmtExpr.E) });
        var stmtBlockUpdate = new BlockStmt(new RangeToken(stmtExpr.S.StartToken, stmtExpr.E.EndToken), new List<Statement>());
        stmtBlockUpdate.Body.Add(stmtExpr.S);
        stmtBlockUpdate.Body.Add(updateStmt);
        return identifierExpr;
      case NestedMatchExpr matchExpr:
        newStmts.Add(varDecl);
        var caseStmts = new List<NestedMatchCaseStmt>();
        foreach (var c in matchExpr.Cases) {
          updateStmt = new UpdateStmt(new RangeToken(c.Body.StartToken, c.Body.StartToken), new List<Expression>() { identifierExpr },
            new List<AssignmentRhs>() { new ExprRhs(c.Body) });
          caseStmts.Add(new NestedMatchCaseStmt(new RangeToken(c.StartToken, c.StartToken), c.Pat, new List<Statement>() {updateStmt}));
        }
        var matchStmt = new NestedMatchStmt(matchExpr.RangeToken, matchExpr.Source, caseStmts, false, matchExpr.Attributes);
        newStmts.Add(matchStmt);
        return identifierExpr;
      case LetOrFailExpr letOrFailExpr:
        newStmts.Add(varDecl);
        var boundIdentifierExpr = new IdentifierExpr(letOrFailExpr.Rhs.StartToken, letOrFailExpr.Lhs.Var.Name);
        var assignSuchThat = new AssignOrReturnStmt(letOrFailExpr.Rhs.RangeToken,  new List<Expression>() { boundIdentifierExpr }, new ExprRhs(letOrFailExpr.Rhs), null, new List<AssignmentRhs>());
        varDecl = new VarDeclStmt(
          new RangeToken(letOrFailExpr.Lhs.Var.StartToken, letOrFailExpr.Rhs.EndToken),
          new List<LocalVariable>() { new(letOrFailExpr.Lhs.Var.RangeToken, letOrFailExpr.Lhs.Var.Name, new InferredTypeProxy(), false) }, assignSuchThat);
        updateStmt = new UpdateStmt(letOrFailExpr.Body.RangeToken, new List<Expression>() { identifierExpr },
          new List<AssignmentRhs>() { new ExprRhs(letOrFailExpr.Body) });
        newStmts.Add(new BlockStmt(letOrFailExpr.RangeToken, new List<Statement>() {varDecl, updateStmt}));
        return identifierExpr;
      case LetExpr letExpr:
        if (letExpr.Exact == false || letExpr.BoundVars.Count() != letExpr.RHSs.Count) {
          // TODO
          foundShortCircuit = true;
          return base.CloneExpr(expr);
        }
        newStmts.Add(varDecl);
        i = 0;
        var blockUpdate = new BlockStmt(letExpr.RangeToken, new List<Statement>());
        foreach (var boundVar in letExpr.BoundVars) {
          identifierExpr = new IdentifierExpr(letExpr.RHSs[i].StartToken, boundVar.Name);
          updateStmt = new UpdateStmt(letExpr.RHSs[i].RangeToken, new List<Expression>() { identifierExpr },
              new List<AssignmentRhs>() { new ExprRhs(letExpr.RHSs[i]) });
          varDecl = new VarDeclStmt(
            new RangeToken(boundVar.StartToken, letExpr.RHSs[i].EndToken),
            new List<LocalVariable>() { new(boundVar.RangeToken, boundVar.Name, new InferredTypeProxy(), false) }, updateStmt);
          blockUpdate.Body.Add(varDecl);
          i += 1;
        }
        identifierExpr = new IdentifierExpr(letExpr.Body.StartToken, tmpVarName);
        updateStmt = new UpdateStmt(letExpr.Body.RangeToken, new List<Expression>() { identifierExpr },
          new List<AssignmentRhs>() { new ExprRhs(letExpr.Body) });
        blockUpdate.Body.Add(updateStmt);
        newStmts.Add(blockUpdate);
        return identifierExpr;
      case ApplySuffix applySuffix:
        if (insideUpdateStatement) {
          break;
        }
        updateStmt = new UpdateStmt(applySuffix.RangeToken, new List<Expression>() { identifierExpr },
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