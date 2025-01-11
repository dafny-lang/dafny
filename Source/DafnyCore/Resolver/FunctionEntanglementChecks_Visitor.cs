using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

class FunctionEntanglementChecks_Visitor : ResolverBottomUpVisitor {
  private readonly ICallable context;
  public bool DoDecreasesChecks;
  public FunctionEntanglementChecks_Visitor(ModuleResolver resolver, ICallable context)
    : base(resolver) {
    Contract.Requires(resolver != null);
    Contract.Requires(context != null);
    this.context = context;
  }

  protected override void VisitOneExpr(Expression expr) {
    if (!DoDecreasesChecks && expr is MemberSelectExpr { Member: Function fn }) {
      if (ModuleDefinition.InSameSCC(context, fn)) {
        resolver.reporter.Error(MessageSource.Resolver, expr.Origin,
          "cannot use naked function in recursive setting. Possible solution: eta expansion.");
      }
    }
  }
}