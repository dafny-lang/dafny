using System;
using System.Collections.Generic;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Dafny.Compilers;

public abstract record IExpression;

public abstract record IStatement;

public record ILiteral(object Literal) : IExpression;

/// <summary>
/// TrSeqSelectExpr from GenericSinglePassCompiler can be used.
/// </summary>
public abstract class IntermediateLanguageCompiler : GenericSinglePassCompiler<IExpression, IList<IStatement>> {

  protected override IExpression EmitThis() {
    throw new System.NotImplementedException();
  }

  protected override IExpression EmitLiteralExpr(LiteralExpr e) {
    return new ILiteral(e.Value);
  }

  protected override IExpression EmitArraySelect(List<Expression> indices, Type elementType, bool inLetExprBody, IExpression array,
    IList<IStatement> wStmts) {
    throw new System.NotImplementedException();
  }

  protected override IExpression EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
    IList<IStatement> wStmts) {
    throw new System.NotImplementedException();
  }

  protected override IExpression EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray, bool inLetExprBody,
    IList<IStatement> wStmts) {
    throw new System.NotImplementedException();
  }

  protected override IExpression TrParenExpr(Expression expr, bool inLetExprBody, IList<IStatement> wStmts) {
    throw new System.NotImplementedException();
  }
}