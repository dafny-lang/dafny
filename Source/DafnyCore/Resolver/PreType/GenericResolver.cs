namespace Microsoft.Dafny;

public interface GenericResolver {
    
  DafnyOptions Options { get; }
  ErrorReporter Reporter { get; }
  Scope<IVariable> Scope { get; }
  Scope<Label> DominatingStatementLabels { get; }
  void ResolveAttributes(IAttributeBearingDeclaration attributedToken, ResolutionContext resolutionContext, bool solveConstraints = false);
  MethodCallInformation ResolveApplySuffix(ApplySuffix applySuffix, ResolutionContext resolutionContext, bool allowMethodCall);
  void ResolveExpression(Expression expression, ResolutionContext resolutionContext);
  void CheckIsLvalue(Expression expression, ResolutionContext resolutionContext);
  void ConstrainTypeExprBool(Expression expression, string message);
  void ResolveStatement(Statement statement, ResolutionContext resolutionContext);
}