using System;
using System.Collections.Generic;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Dafny.Compilers;

public abstract record IExpression;

public record ILiteral(object Literal) : IExpression;

public abstract class IntermediateLanguageCompiler : GenericSinglePassCompiler<IExpression> {
  
  public override string PublicIdProtect(string name) {
    return name;
  }
  
  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    throw new System.NotImplementedException();
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    throw new System.NotImplementedException();
  }

  protected internal override IExpression TrExpr(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wStmts) {
    return expr switch {
      LiteralExpr literalExpr => new ILiteral(literalExpr.Value),
      _ => throw new NotImplementedException()
    };
  }

  protected override IExpression EmitThis() {
    throw new System.NotImplementedException();
  }

  protected override IExpression EmitLiteralExpr(LiteralExpr e) {
    throw new System.NotImplementedException();
  }

  protected override IExpression EmitArraySelect(List<Expression> indices, Type elementType, bool inLetExprBody, IExpression array,
    ConcreteSyntaxTree wStmts) {
    throw new System.NotImplementedException();
  }

  protected override IExpression EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
    ConcreteSyntaxTree wStmts) {
    throw new System.NotImplementedException();
  }

  protected override IExpression EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray, bool inLetExprBody,
    ConcreteSyntaxTree wStmts) {
    throw new System.NotImplementedException();
  }

  protected override IExpression TrParenExpr(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wStmts) {
    throw new System.NotImplementedException();
  }
}