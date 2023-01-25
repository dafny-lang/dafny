using System.Collections.Generic;

namespace Microsoft.Dafny.Compilers;

public abstract record IExpression;

public record ILiteral(object Literal) : IExpression;

public abstract record IStatement;

public abstract record IType;

/// <summary>
/// In this class, members from GenericSinglePassCompiler can be used.
///
/// An example method that used to be in ConcreteSinglePassCompiler (which was called SinglePassCompiler),
/// but is now moved to GenericSinglePassCompiler, is MultiAssignment, was was called 'EmitMultiAssignment' before.
///
/// If there's any logic in ConcreteSinglePassCompiler that seems interesting for IntermediateLanguageCompiler, please
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
public abstract class IntermediateLanguageCompiler : GenericSinglePassCompiler<IExpression, IList<IStatement>, IStatement, IType> {

  protected override IExpression This() {
    throw new System.NotImplementedException();
  }

  protected override IExpression LiteralExpr(LiteralExpr e) {
    return new ILiteral(e.Value);
  }

  protected override IExpression ArraySelect(List<Expression> indices, Type elementType, bool inLetExprBody, IExpression array,
    IList<IStatement> wStmts) {
    throw new System.NotImplementedException();
  }

  protected override IExpression IndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
    IList<IStatement> wStmts) {
    throw new System.NotImplementedException();
  }

  protected override IExpression SeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray, bool inLetExprBody,
    IList<IStatement> wStmts) {
    throw new System.NotImplementedException();
  }

  protected override IExpression TrParenExpr(Expression expr, bool inLetExprBody, IList<IStatement> wStmts) {
    return TrExpr(expr, inLetExprBody, wStmts);
  }
}