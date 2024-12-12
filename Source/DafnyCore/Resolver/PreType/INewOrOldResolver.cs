using System.Collections.Generic;

namespace Microsoft.Dafny;

public interface INewOrOldResolver {

  DafnyOptions Options { get; }
  ErrorReporter Reporter { get; }
  Scope<IVariable> Scope { get; }
  Scope<Label> DominatingStatementLabels { get; }
  Scope<Statement> EnclosingStatementLabels { get; set; }
  List<Statement> LoopStack { get; set; }
  void ResolveAttributes(IAttributeBearingDeclaration attributedToken, ResolutionContext resolutionContext, bool solveConstraints = false);
  MethodCallInformation ResolveApplySuffix(ApplySuffix applySuffix, ResolutionContext resolutionContext, bool allowMethodCall);
  void ResolveExpression(Expression expression, ResolutionContext resolutionContext);
  void CheckIsLvalue(Expression expression, ResolutionContext resolutionContext);
  void ConstrainTypeExprBool(Expression expression, string message);
  void ResolveStatement(Statement statement, ResolutionContext resolutionContext);
  void ResolveTypeRhs(TypeRhs typeRhs, Statement statement, ResolutionContext resolutionContext);
  void ResolveBlockStatement(BlockStmt blockS, ResolutionContext resolutionContext);

  Scope<Thing>.PushResult ScopePushAndReport<Thing>(Scope<Thing> scope, string name, Thing thing, IOrigin tok,
    string kind) where Thing : class;

  public void ScopePushAndReport(Scope<IVariable> scope, IVariable v, string kind) {
    ScopePushAndReport(scope, v.Name, v, v.Tok, kind);
  }

  void ResolveStatementWithLabels(Statement statement, ResolutionContext resolutionContext);
  void ResolveFrameExpression(
    FrameExpression frameExpression,
    FrameExpressionUse frameExpressionUse,
    ResolutionContext context);

  public Expression ResolveNameSegment(NameSegment expr, bool isLastNameSegment, List<ActualBinding> args,
    ResolutionContext resolutionContext, bool allowMethodCall, bool complain = true);

  public Expression ResolveDotSuffix(ExprDotName expr, bool allowStaticReferenceToInstance, bool isLastNameSegment, List<ActualBinding> args,
    ResolutionContext resolutionContext, bool allowMethodCall);
}