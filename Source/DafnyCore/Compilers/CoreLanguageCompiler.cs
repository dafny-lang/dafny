using System.Collections.Generic;

namespace Microsoft.Dafny.Compilers;

public abstract record CoreExpression;

public record CoreLiteral(object Literal) : CoreExpression;
public record CoreVariable(string Name) : CoreExpression;

public abstract record CoreStatement;

public record CoreExpressionStatement(CoreExpression Expression) : CoreStatement;

public abstract record CoreType;

/// <summary>
/// In this class, members from GenericSinglePassCompiler can be used.
///
/// An example method that used to be in ConcreteSinglePassCompiler (which was called SinglePassCompiler),
/// but is now moved to GenericSinglePassCompiler, is MultiAssignment, was was called 'EmitMultiAssignment' before.
///
/// If there's any logic in ConcreteSinglePassCompiler that seems interesting for CoreLanguageCompiler, please
/// move it to GenericSinglePassCompiler.
///
/// Sometimes we want to use a method from ConcreteSinglePassCompiler in GenericSinglePassCompiler, for which we add
/// an abstract method to GenericSinglePassCompiler. However, generally methods in ConcreteSinglePassCompiler have the form
/// void EmitSomething(..., ConcreteSyntaxTree wr);
/// 
/// And when using them to implement an abstract from GenericSinglePassCompiler, they first have to be transformed to
/// ConcreteSyntaxTree Something(...);
///
/// This is a translation that can be done rather mechanically, but it might take some getting used to.
///
/// Some of the code in ConcreteSinglePassCompiler involves mostly string manipulation, and it might not be interesting
/// to move it to GenericSinglePassCompiler since than most of the logic won't be moveable.
/// </summary>
public class CoreLanguageCompiler : GenericSinglePassCompiler<CoreExpression, IList<CoreStatement>, CoreStatement, CoreType> {

  protected override CoreExpression TrParenExpr(Expression expr, bool inLetExprBody, IList<CoreStatement> wStmts) {
    return TrExpr(expr, inLetExprBody, wStmts);
  }
  
  protected override CoreExpression LiteralExpr(LiteralExpr e) {
    return new CoreLiteral(e.Value);
  }

  protected override CoreStatement AsStatement(CoreExpression expression) {
    return new CoreExpressionStatement(expression);
  }

  protected override CoreExpression Variable(string name) {
    return new CoreVariable(name);
  }

  protected override IList<CoreStatement> CreateStatementList() {
    return new List<CoreStatement>();
  }
  
  internal override CoreType TypeName(Type type, IToken tok, MemberDecl member = null) {
    throw new System.NotImplementedException();
  }

  protected override CoreExpression This() {
    throw new System.NotImplementedException();
  }

  protected override CoreExpression ArraySelect(List<Expression> indices, Type elementType, bool inLetExprBody, CoreExpression array,
    IList<CoreStatement> wStmts) {
    throw new System.NotImplementedException();
  }

  protected override CoreExpression IndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
    IList<CoreStatement> wStmts) {
    throw new System.NotImplementedException();
  }

  protected override CoreExpression SeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray, bool inLetExprBody,
    IList<CoreStatement> wStmts) {
    throw new System.NotImplementedException();
  }

  protected override CoreStatement VariableDeclaration(string name, Type type, IToken token, CoreExpression initialValue) {
    throw new System.NotImplementedException();
  }

  protected override string EmitAssignmentLhs(Expression e, IList<CoreStatement> wStmts) {
    throw new System.NotImplementedException();
  }

  protected override ILvalue MemberSelect(CoreExpression obj, Type objType, MemberDecl member, List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap,
    Type expectedType, string additionalCustomParameter = null, bool internalAccess = false) {
    throw new System.NotImplementedException();
  }

  protected override ILvalue ArraySelectAsLvalue(string array, List<CoreExpression> indices, Type elementType) {
    throw new System.NotImplementedException();
  }

  // TODO should be implemented in GenericSinglePassCompiler
  protected internal override CoreExpression TrExpr(Expression expr, bool inLetExprBody, IList<CoreStatement> wStmts) {
    throw new System.NotImplementedException();
  }
}