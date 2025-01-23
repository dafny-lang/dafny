using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols;

internal class LocalVariableDeclarationVisitor(ILogger logger, ScopeSymbol rootBlock) : SyntaxTreeVisitor {
  // TODO support cancellation

  public void Resolve(BlockStmt blockStatement) {
    // The base is directly visited to avoid doubly nesting the root block of the method.
    base.Visit(blockStatement);
  }

  public void Resolve(Expression bodyExpression) {
    // The base is directly visited to avoid doubly nesting the root block of the method.
    base.Visit(bodyExpression);
  }

  public override void VisitUnknown(object node, IOrigin token) {
    logger.LogTrace("encountered unknown syntax node of type {NodeType} in {Filename}@({Line},{Column})",
      node.GetType(), token.GetDocumentFileName(), token.line, token.col);
  }

  public override void Visit(BlockStmt blockStatement) {
    var oldBlock = rootBlock;
    rootBlock = new ScopeSymbol(rootBlock, blockStatement);
    oldBlock.Symbols.Add(rootBlock);
    base.Visit(blockStatement);
    rootBlock = oldBlock;
  }

  public override void Visit(LocalVariable localVariable) {
    rootBlock.Symbols.Add(new VariableSymbol(rootBlock, localVariable));
  }

  public override void Visit(LambdaExpr lambdaExpression) {
    ProcessBoundVariableBearingExpression(lambdaExpression, () => base.Visit(lambdaExpression));
  }

  public override void Visit(ForallExpr forallExpression) {
    ProcessBoundVariableBearingExpression(forallExpression, () => base.Visit(forallExpression));
  }

  public override void Visit(ExistsExpr existExpression) {
    ProcessBoundVariableBearingExpression(existExpression, () => base.Visit(existExpression));
  }

  public override void Visit(SetComprehension setComprehension) {
    ProcessBoundVariableBearingExpression(setComprehension, () => base.Visit(setComprehension));
  }

  public override void Visit(MapComprehension mapComprehension) {
    ProcessBoundVariableBearingExpression(mapComprehension, () => base.Visit(mapComprehension));
  }

  public override void Visit(LetExpr letExpression) {
    ProcessBoundVariableBearingExpression(letExpression, () => base.Visit(letExpression));
  }

  private void ProcessBoundVariableBearingExpression<TExpr>(
    TExpr boundVarExpression, System.Action baseVisit
  ) where TExpr : Expression, IBoundVarsBearingExpression {
    var oldBlock = rootBlock;
    // To prevent two scope symbols from pointing to the same node,
    // (this crashes `declarations[nodes]` later on)
    // we reuse the existing scope symbol if it happens to be a top-level
    // bounded variable bearing expression that otherwise would create a new scope symbol
    if (rootBlock.Node != boundVarExpression) {
      rootBlock = new ScopeSymbol(rootBlock, boundVarExpression);
      oldBlock.Symbols.Add(rootBlock);
    }
    foreach (var parameter in boundVarExpression.AllBoundVars) {
      rootBlock.Symbols.Add(ProcessBoundVar(rootBlock, parameter));
    }
    baseVisit();
    rootBlock = oldBlock;
  }

  private static VariableSymbol ProcessBoundVar(Symbol scope, BoundVar formal) {
    return new VariableSymbol(scope, formal);
  }
}