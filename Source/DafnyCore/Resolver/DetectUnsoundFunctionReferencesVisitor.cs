using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

class DetectUnsoundFunctionReferencesVisitor : ResolverBottomUpVisitor {
  private readonly ICallable context;
  private bool doDecreasesChecks;
  private DetectUnsoundFunctionReferencesVisitor(ModuleResolver resolver, ICallable context)
    : base(resolver) {
    Contract.Requires(resolver != null);
    Contract.Requires(context != null);
    this.context = context;
  }

  public static void Check(ICallable callable, ModuleResolver resolver) {
    var visitor = new DetectUnsoundFunctionReferencesVisitor(resolver, callable);
    visitor.doDecreasesChecks = false;
    if (callable is Function function) {
      visitor.VisitFunctionWithoutByMethod(function);
    } else {
      visitor.Visit(callable);
    }
    visitor.doDecreasesChecks = true;
    visitor.Visit(callable.Decreases.Expressions);
  }

  protected override void VisitOneExpr(Expression expr) {
    if (expr is MemberSelectExpr { Member: Function fn }) {
      if (fn.ReadsDoubleStar) {
        resolver.reporter.Error(MessageSource.Resolver, expr.Origin,
          "a function declared with 'reads **' can only be used if applied to arguments");
      }

      if (!doDecreasesChecks && ModuleDefinition.InSameSCC(context, fn)) {
        resolver.reporter.Error(MessageSource.Resolver, expr.Origin,
          "cannot use naked function in recursive setting. Possible solution: eta expansion.");
      }

    }

    if (doDecreasesChecks && expr is FunctionCallExpr callExpr && ModuleDefinition.InSameSCC(context, callExpr.Function)) {
      string msg;
      if (context == callExpr.Function) {
        msg = "a decreases clause is not allowed to call the enclosing function";
      } else {
        msg = $"the decreases clause of {context.WhatKind} '{context.NameRelativeToModule}' is not allowed to call '{callExpr.Function}', " +
              "because they are mutually recursive";
      }

      resolver.reporter.Error(MessageSource.Resolver, callExpr.Origin, msg);
    }
  }
}
