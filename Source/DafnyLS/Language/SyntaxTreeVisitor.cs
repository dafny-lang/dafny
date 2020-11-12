namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Base syntax tree visitor implementation that visits all nodes.
  /// </summary>
  public abstract class SyntaxTreeVisitor {
    // TODO Double-dispatching would be convenient here, but requirees adaptions to the AST.
    // TODO Is visiting Attributes necessary, i.e., does it belong to the AST?

    /// <summary>
    /// This method is invoked as soon as the visitor encounters an unknown syntax node.
    /// </summary>
    /// <param name="node">The unknown node that is being visited.</param>
    /// <param name="token">The token asociated with the unknown node.</param>
    public abstract void VisitUnknown(object node, Boogie.IToken token);

    public virtual void Visit(Dafny.Program program) {
      foreach(var module in program.Modules()) {
        Visit(module);
      }
    }

    public virtual void Visit(ModuleDefinition moduleDefinition) {
      foreach(var topLevelDeclaration in moduleDefinition.TopLevelDecls) {
        Visit(topLevelDeclaration);
      }
    }

    public virtual void Visit(TopLevelDecl topLevelDeclaration) {
      switch(topLevelDeclaration) {
      case ClassDecl classDeclaration:
        Visit(classDeclaration);
        break;
      case ModuleDecl moduleDeclaration:
      case DatatypeDecl dataTypeDeclaration:
      case ValuetypeDecl valueTypeDeclaration:
      case OpaqueTypeDecl opaqueTypeDeclaration:
      case NewtypeDecl newTypeDeclaration:
      case TypeSynonymDecl typeSynonymDeclaration:
      default:
        VisitUnknown(topLevelDeclaration, topLevelDeclaration.tok);
        break;
      }
    }

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
        VisitUnknown(memberDeclaration, memberDeclaration.tok);
        break;
      }
    }

    public virtual void Visit(Field field) {
      foreach(var expression in field.SubExpressions) {
        Visit(expression);
      }
    }

    public virtual void Visit(Method method) {
      foreach(var typeArgument in method.TypeArgs) {
        Visit(typeArgument);
      }
      foreach(var inDefinition in method.Ins) {
        Visit(inDefinition);
      }
      foreach(var outDefinition in method.Outs) {
        Visit(outDefinition);
      }
      VisitNullableAttributes(method.Attributes);
      foreach(var requirement in method.Req) {
        Visit(requirement);
      }
      foreach(var ensurement in method.Ens) {
        Visit(ensurement);
      }
      Visit(method.Decreases);
      VisitNullableBlock(method.Body);
    }

    public virtual void Visit(Constructor constructor) {
      foreach(var outDefinition in constructor.Outs) {
        Visit(outDefinition);
      }
      VisitNullableBlock(constructor.Body);
    }

    public virtual void Visit(Function function) {
      VisitNullableExpression(function.Body);
      foreach(var typeArgument in function.TypeArgs) {
        Visit(typeArgument);
      }
      foreach(var formal in function.Formals) {
        Visit(formal);
      }
      foreach(var read in function.Reads) {
        Visit(read);
      }
      foreach(var requirement in function.Req) {
        Visit(requirement);
      }
      foreach(var ensurement in function.Ens) {
        Visit(ensurement);
      }
      Visit(function.Decreases);
    }

    public virtual void Visit(NonglobalVariable nonGlobalVariable) {
    }

    public virtual void Visit(Formal formal) {
    }

    public virtual void Visit(LocalVariable localVariable) {
      VisitNullableAttributes(localVariable.Attributes);
    }

    private void VisitNullableAttributes(Attributes? attributes) {
      if(attributes != null) {
        Visit(attributes);
      }
    }

    public virtual void Visit(Attributes attributes) {
      foreach(var argument in attributes.Args) {
        Visit(argument);
      }
    }

    public virtual void Visit(ExprRhs expressionRhs) {
      VisitNullableAttributes(expressionRhs.Attributes);
      Visit(expressionRhs.Expr);
    }

    public virtual void Visit(AssignmentRhs assignmentRhs) {
      switch(assignmentRhs) {
      case ExprRhs expressionRhs:
        Visit(expressionRhs);
        break;
      case TypeRhs typeRhs:
        Visit(typeRhs);
        break;
      default:
        VisitUnknown(assignmentRhs, assignmentRhs.Tok);
        break;
      }
    }

    public virtual void Visit(TypeRhs typeRhs) {
      VisitNullableAttributes(typeRhs.Attributes);
      if(typeRhs.Arguments != null) {
        foreach(var argument in typeRhs.Arguments) {
          Visit(argument);
        }
      }
      if(typeRhs.ArrayDimensions != null) {
        foreach(var dimension in typeRhs.ArrayDimensions) {
          Visit(dimension);
        }
      }
    }

    public virtual void Visit(BlockStmt blockStatement) {
      VisitNullableAttributes(blockStatement.Attributes);
      foreach(var statement in blockStatement.Body) {
        Visit(statement);
      }
    }

    private void VisitNullableBlock(BlockStmt? blockStatement) {
      if(blockStatement != null) {
        Visit(blockStatement);
      }
    }

    public virtual void Visit(WhileStmt whileStatement) {
      Visit(whileStatement.Guard);
      VisitNullableAttributes(whileStatement.Attributes);
      foreach(var invariant in whileStatement.Invariants) {
        Visit(invariant);
      }
      // TODO Visit Decreases, Mod?
      VisitNullableBlock(whileStatement.Body);
    }

    public virtual void Visit(IfStmt ifStatement) {
      Visit(ifStatement.Guard);
      VisitNullableAttributes(ifStatement.Attributes);
      VisitNullableBlock(ifStatement.Thn);
      VisitNullableStatement(ifStatement.Els);
    }

    public virtual void Visit(VarDeclStmt variableDeclarationStatement) {
      foreach(var localVariable in variableDeclarationStatement.Locals) {
        Visit(localVariable);
      }
      if(variableDeclarationStatement.Update != null) {
        Visit(variableDeclarationStatement.Update);
      }
    }

    public virtual void Visit(UpdateStmt updateStatement) {
      VisitNullableAttributes(updateStatement.Attributes);
      foreach(var leftHandSide in updateStatement.Lhss) {
        Visit(leftHandSide);
      }
      foreach(var rightHandSide in updateStatement.Rhss) {
        Visit(rightHandSide);
      }
    }

    public virtual void Visit(Statement statement) {
      switch(statement) {
      case IfStmt ifStatement:
        Visit(ifStatement);
        break;
      case WhileStmt whileStatement:
        Visit(whileStatement);
        break;
      case VarDeclStmt variableDeclarationStatement:
        Visit(variableDeclarationStatement);
        break;
      case UpdateStmt updateStatement:
        Visit(updateStatement);
        break;
      case AssertStmt assertStatement:
        Visit(assertStatement);
        break;
      case ReturnStmt returnStatement:
        Visit(returnStatement);
        break;
      case BlockStmt blockStatement:
        Visit(blockStatement);
        break;
      case MatchStmt matchStatement:
        Visit(matchStatement);
        break;
      case NestedMatchStmt nestedMatchStatement:
        Visit(nestedMatchStatement);
        break;
      case ForallStmt forAllStatement:
        Visit(forAllStatement);
        break;
      case PrintStmt printStatement:
        Visit(printStatement);
        break;
      default:
        VisitUnknown(statement, statement.Tok);
        break;
      }
    }

    private void VisitNullableStatement(Statement? statement) {
      if(statement != null) {
        Visit(statement);
      }
    }

    public virtual void Visit(AssertStmt assertStatement) {
      VisitNullableAttributes(assertStatement.Attributes);
      Visit(assertStatement.Expr);
      VisitNullableStatement(assertStatement.Proof);
    }

    public virtual void Visit(ReturnStmt returnStatement) {
      VisitNullableAttributes(returnStatement.Attributes);
      foreach(var rhs in returnStatement.rhss) {
        Visit(rhs);
      }
    }

    public virtual void Visit(MatchStmt matchStatement) {
      VisitNullableAttributes(matchStatement.Attributes);
      Visit(matchStatement.Source);
      foreach(var matchCase in matchStatement.Cases) {
        Visit(matchCase);
      }
    }

    public virtual void Visit(MatchCaseStmt matchCaseStatement) {
      foreach(var argument in matchCaseStatement.Arguments) {
        Visit(argument);
      }
      foreach(var body in matchCaseStatement.Body) {
        Visit(body);
      }
    }

    public virtual void Visit(NestedMatchStmt nestedMatchStatement) {
      VisitNullableAttributes(nestedMatchStatement.Attributes);
      Visit(nestedMatchStatement.Source);
      foreach(var nestedMatchCase in nestedMatchStatement.Cases) {
        Visit(nestedMatchCase);
      }
    }

    public virtual void Visit(NestedMatchCaseStmt nestedMatchCaseStatement) {
      foreach(var body in nestedMatchCaseStatement.Body) {
        Visit(body);
      }
    }

    public virtual void Visit(ForallStmt forAllStatement) {
      VisitNullableAttributes(forAllStatement.Attributes);
      VisitNullableStatement(forAllStatement.Body);
    }

    public virtual void Visit(PrintStmt printStatement) {
      VisitNullableAttributes(printStatement.Attributes);
      foreach(var argument in printStatement.Args) {
        Visit(argument);
      }
    }

    public virtual void Visit(Expression expression) {
      switch(expression) {
      case LiteralExpr literalExpression:
        Visit(literalExpression);
        break;
      case ThisExpr thisExpression:
        Visit(thisExpression);
        break;
      case IdentifierExpr identifierExpression:
        Visit(identifierExpression);
        break;
      case SeqSelectExpr sequenceSelectExpression:
        Visit(sequenceSelectExpression);
        break;
      case UnaryExpr unaryExpression:
        Visit(unaryExpression);
        break;
      case BinaryExpr binaryExpression:
        Visit(binaryExpression);
        break;
      case TernaryExpr ternaryExpression:
        Visit(ternaryExpression);
        break;
      case NameSegment nameSegment:
        Visit(nameSegment);
        break;
      case ParensExpression parenthesesExpression:
        Visit(parenthesesExpression);
        break;
      case ExprDotName expressionDotName:
        Visit(expressionDotName);
        break;
      case ApplySuffix applySuffix:
        Visit(applySuffix);
        break;
      case ChainingExpression chainingExpression:
        Visit(chainingExpression);
        break;
      case NegationExpression negationExpression:
        Visit(negationExpression);
        break;
      case OldExpr oldExpression:
        Visit(oldExpression);
        break;
      case ITEExpr ifThenElseExpression:
        Visit(ifThenElseExpression);
        break;
      case ForallExpr forAllExpression:
        Visit(forAllExpression);
        break;
      case NestedMatchExpr nestedMatchExpression:
        Visit(nestedMatchExpression);
        break;
      case SetDisplayExpr setDisplayExpression:
        Visit(setDisplayExpression);
        break;
      case MultiSetDisplayExpr multiSetDisplayExpression:
        Visit(multiSetDisplayExpression);
        break;
      case SeqDisplayExpr sequenceDisplayExpression:
        Visit(sequenceDisplayExpression);
        break;
      default:
        VisitUnknown(expression, expression.tok);
        break;
      }
    }

    private void VisitNullableExpression(Expression? expression) {
      if(expression != null) {
        Visit(expression);
      }
    }

    public virtual void Visit(AutoGhostIdentifierExpr autoGhostIdentifierExpression) {
    }

    public virtual void Visit(LiteralExpr literalExpression) {
    }

    public virtual void Visit(IdentifierExpr identifierExpression) {
    }

    public virtual void Visit(ApplySuffix applySuffix) {
      Visit(applySuffix.Lhs);
      foreach(var argument in applySuffix.Args) {
        Visit(argument);
      }
    }

    public virtual void Visit(NameSegment nameSegment) {
    }

    public virtual void Visit(AliasModuleDecl aliasModuleDecl) {
    }

    public virtual void Visit(ExprDotName expressionDotName) {
      Visit(expressionDotName.Lhs);
    }

    public virtual void Visit(ThisExpr thisExpression) {
    }

    public virtual void Visit(DisplayExpression displayExpression) {
    }

    public virtual void Visit(ComprehensionExpr comprehensionExpression) {
    }

    public virtual void Visit(AttributedExpression attributedExpression) {
      VisitNullableAttributes(attributedExpression.Attributes);
      Visit(attributedExpression.E);
    }

    public virtual void Visit(SeqSelectExpr sequenceSelectExpression) {
      VisitNullableExpression(sequenceSelectExpression.Seq);
      VisitNullableExpression(sequenceSelectExpression.E0);
      VisitNullableExpression(sequenceSelectExpression.E1);
    }

    public virtual void Visit(TypeParameter typeParameter) {
    }

    public virtual void Visit(ParensExpression parenthesesExpression) {
      Visit(parenthesesExpression.E);
    }

    public virtual void Visit(UnaryExpr unaryExpression) {
      VisitNullableExpression(unaryExpression.E);
    }

    public virtual void Visit(BinaryExpr binaryExpression) {
      VisitNullableExpression(binaryExpression.E0);
      VisitNullableExpression(binaryExpression.E1);
    }

    public virtual void Visit(TernaryExpr ternaryExpression) {
      VisitNullableExpression(ternaryExpression.E0);
      VisitNullableExpression(ternaryExpression.E1);
      VisitNullableExpression(ternaryExpression.E2);
    }

    public virtual void Visit(ChainingExpression chainingExpression) {
      foreach(var operand in chainingExpression.Operands) {
        Visit(operand);
      }
    }

    public virtual void Visit(NegationExpression negationExpression) {
      Visit(negationExpression.E);
    }

    public virtual void Visit(OldExpr oldExpression) {
      Visit(oldExpression.E);
    }

    public virtual void Visit(ITEExpr ifThenElseExpression) {
      Visit(ifThenElseExpression.Test);
      Visit(ifThenElseExpression.Thn);
      Visit(ifThenElseExpression.Els);
    }

    public virtual void Visit(ForallExpr forAllExpression) {
      VisitNullableAttributes(forAllExpression.Attributes);
      VisitNullableExpression(forAllExpression.Range);
      Visit(forAllExpression.Term);
    }

    public virtual void Visit(NestedMatchExpr nestedMatchExpression) {
      Visit(nestedMatchExpression.Source);
      foreach(var nestedMatchCaseExpression in nestedMatchExpression.Cases) {
        Visit(nestedMatchCaseExpression);
      }
    }

    public virtual void Visit(NestedMatchCaseExpr nestedMatchCaseExpression) {
      Visit(nestedMatchCaseExpression.Pat);
      Visit(nestedMatchCaseExpression.Body);
    }

    public virtual void Visit(SetDisplayExpr setDisplayExpression) {
      foreach(var element in setDisplayExpression.Elements) {
        Visit(element);
      }
    }

    public virtual void Visit(MultiSetDisplayExpr multiSetDisplayExpression) {
      foreach(var element in multiSetDisplayExpression.Elements) {
        Visit(element);
      }
    }

    public virtual void Visit(SeqDisplayExpr sequenceDisplayExpression) {
      foreach(var element in sequenceDisplayExpression.Elements) {
        Visit(element);
      }
    }

    public virtual void Visit(Specification<Expression> specification) {
      VisitNullableAttributes(specification.Attributes);
      foreach(var expression in specification.Expressions) {
        Visit(expression);
      }
    }

    public virtual void Visit(FrameExpression frameExpression) {
    }

    public virtual void Visit(ExtendedPattern extendedPattern) {
      // TODO Visit the various pattern types.
    }
  }
}
