using Microsoft.Dafny;
using System;

namespace DafnyLS.Language {
  /// <summary>
  /// Base syntax tree visitor implementation that visits all nodes in post-order traversal.
  /// </summary>
  internal class SyntaxTreeVisitor {
    // TODO ensure that all Visit(...) methods cover all the nested syntax elements in post-order traversal.
    // TODO Double-dispatching would be convenient here, but requirees adaptions to the AST.

    public virtual void Visit(ClassDecl classDeclaration) {
      foreach(var member in classDeclaration.Members) {
        Visit(member);
      }
    }

    public virtual void Visit(MemberDecl memberDeclaration) {
      switch(memberDeclaration) {
      case Field field:
        Visit(field);
        break;
      case Function function:
        Visit(function);
        break;
      case Method method:
        Visit(method);
        break;
      default:
        throw new ArgumentException($"unknown member declaration type {memberDeclaration.GetType()}", nameof(memberDeclaration));
      }
    }

    public virtual void Visit(Field field) {
      foreach(var expression in field.SubExpressions) {
        Visit(expression);
      }
    }

    public virtual void Visit(Method method) {
      foreach(var outDefinition in method.Outs) {
        Visit(outDefinition);
      }
      Visit(method.Body);
    }

    public virtual void Visit(Constructor constructor) {
      foreach(var outDefinition in constructor.Outs) {
        Visit(outDefinition);
      }
      Visit(constructor.Body);
    }

    public virtual void Visit(Function function) {
      Visit(function.Body);
    }


    public virtual void Visit(NonglobalVariable nonGlobalVariable) {
    }

    public virtual void Visit(Formal formal) {
    }

    public virtual void Visit(LocalVariable localVariable) {
      Visit(localVariable.Attributes);
    }

    public virtual void Visit(Attributes attributes) {
      foreach(var argument in attributes.Args) {
        Visit(argument);
      }
    }


    public virtual void Visit(AssignmentRhs assignmentRhs) {
      Visit(assignmentRhs.Attributes);
    }

    public virtual void Visit(TypeRhs typeRhs) {
      Visit(typeRhs.Attributes);
    }


    public virtual void Visit(BlockStmt blockStatement) {
      Visit(blockStatement.Attributes);
      foreach(var statement in blockStatement.Body) {
        Visit(statement);
      }
    }

    public virtual void Visit(WhileStmt whileStatement) {
      Visit(whileStatement.Guard);
      Visit(whileStatement.Attributes);
      foreach(var invariant in whileStatement.Invariants) {
        Visit(invariant);
      }
      // TODO Visit Decreases, Mod?
      Visit(whileStatement.Body);
    }

    public virtual void Visit(IfStmt ifStatement) {
      Visit(ifStatement.Guard);
      Visit(ifStatement.Attributes);
      Visit(ifStatement.Thn);
      Visit(ifStatement.Els);
    }

    public virtual void Visit(Statement statement) {
      switch(statement) {
      case IfStmt ifStatement:
        Visit(ifStatement);
        break;
      case WhileStmt whileStatement:
        Visit(whileStatement);
        break;
      default:
        throw new ArgumentException($"encountered unknown statement type {statement.GetType()}", nameof(statement));
      }
    }


    public virtual void Visit(Expression expression) {
      switch(expression) {
      case LiteralExpr literalExpression:
        Visit(literalExpression);
        break;
      //case DatatypeValue dataTypeValue:
      //  Visit(dataTypeValue);
      //  break;
      case ThisExpr thisExpression:
        Visit(thisExpression);
        break;
      case IdentifierExpr identifierExpression:
        Visit(identifierExpression);
        break;
      //case DisplayExpression displayExpression:
      //  Visit(displayExpression);
      //  break;
      //case MapDisplayExpr mapDisplayExpression:
      //  Visit(mapDisplayExpression);
      //  break;
      //case MemberSelectExpr memberSelectExpression:
      //  Visit(memberSelectExpression);
      //  break;
      //case SeqSelectExpr sequenceSelectExpression:
      //  Visit(sequenceSelectExpression);
      //  break;
      //case MultiSelectExpr multiSelectExpression:
      //  Visit(multiSelectExpression);
      //  break;
      //case SeqUpdateExpr sequenceUpdateExpression:
      //  Visit(sequenceUpdateExpression);
      //  break;
      //case MultiSetFormingExpr multiSetFormingExpression:
      //  Visit(multiSetFormingExpression);
      //  break;
      //case OldExpr oldExpression:
      //  Visit(oldExpression);
      //  break;
      //case UnchangedExpr unchangedExpr:
      //  Visit(unchangedExpr);
      //  break;
      //case UnaryExpr unaryExpression:
      //  Visit(unaryExpression);
      //  break;
      //case BinaryExpr binaryExpression:
      //  Visit(binaryExpression);
      //  break;
      //case TernaryExpr ternaryExpression:
      //  Visit(ternaryExpression);
      //  break;
      //case LetExpr letExpression:
      //  Visit(letExpression);
      //  break;
      //case NamedExpr namedExpression:
      //  Visit(namedExpression);
      //  break;
      //case ComprehensionExpr comprehensionExpression:
      //  Visit(comprehensionExpression);
      //  break;
      //case WildcardExpr wildcardExpression:
      //  Visit(wildcardExpression);
      //  break;
      //case StmtExpr statementExpression:
      //  Visit(statementExpression);
      //  break;
      //case ITEExpr iteExpression:
      //  Visit(iteExpression);
      //  break;
      //case MatchExpr matchExpression:
      //  Visit(matchExpression);
      //  break;
      //case BoxingCastExpr boxingCastExpression:
      //  Visit(boxingCastExpression);
      //  break;
      //case UnboxingCastExpr unboxingCastExpression:
      //  Visit(unboxingCastExpression);
      //  break;
      //case ConcreteSyntaxExpression concreteSyntaxExpression:
      //  Visit(concreteSyntaxExpression);
      //  break;
      default:
        throw new ArgumentException($"encountered unknown expression type {expression.GetType()}", nameof(expression));
      }
    }

    public virtual void Visit(AutoGhostIdentifierExpr autoGhostIdentifierExpression) {
    }

    public virtual void Visit(LiteralExpr literalExpression) {
    }

    public virtual void Visit(IdentifierExpr identifierExpression) {
    }

    public virtual void Visit(ApplySuffix applySuffix) {
    }

    public virtual void Visit(NameSegment nameSegment) {
    }

    public virtual void Visit(ModuleDefinition moduleDefinition) {
    }

    public virtual void Visit(AliasModuleDecl aliasModuleDecl) {
    }

    public virtual void Visit(ExprDotName expressionDotName) {
    }

    public virtual void Visit(ThisExpr thisExpression) {
    }

    public virtual void Visit(DisplayExpression displayExpression) {
    }

    public virtual void Visit(ComprehensionExpr comprehensionExpression) {
    }

    public virtual void Visit(AttributedExpression attributedExpression) {

    }
  }
}
