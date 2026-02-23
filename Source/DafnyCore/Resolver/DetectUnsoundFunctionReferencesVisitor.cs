using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// This class checks three conditions:
///   0. A function declared with `reads **` is never used naked (i.e., every use of it is applied to arguments)
///   1. A function is never used naked in its own definition (that is, anywhere in the definition of itself or of a mutually recursive callable)
///   2. The decreases clause of a function never makes any recursive or mutually recursive calls to the function itself
/// </summary>
class DetectUnsoundFunctionReferencesVisitor : ResolverBottomUpVisitor {
  private readonly ICallable context;

  private enum Checks { Check0, Check0And1, Check2 }
  private Checks whichChecks;

  private DetectUnsoundFunctionReferencesVisitor(ModuleResolver resolver, ICallable context)
    : base(resolver) {
    Contract.Requires(resolver != null);
    Contract.Requires(context != null);
    this.context = context;
  }

  public static void Check(ICallable callable, ModuleResolver resolver) {
    var visitor = new DetectUnsoundFunctionReferencesVisitor(resolver, callable);
    if (callable is Function function) {
      visitor.whichChecks = Checks.Check0And1;
      visitor.VisitFunctionWithoutByMethod(function);
      if (function.ByMethodBody != null) {
        // don't do check 1 in the by-method clause, since the by-method sits strictly above its function in the call graph
        visitor.whichChecks = Checks.Check0;
        visitor.Visit(function.ByMethodBody);
      }
      // visit the "decreases" clause again, this time performing check 2
      visitor.whichChecks = Checks.Check2;
      visitor.Visit(callable.Decreases.Expressions);

    } else {
      // for the non-function, just performs checks 0 and 1
      visitor.whichChecks = Checks.Check0And1;
      visitor.Visit(callable);
    }
  }

  protected override void VisitOneExpr(Expression expr) {
    if (expr is MemberSelectExpr { Member: Function fn }) {
      // Check 0
      if (whichChecks is Checks.Check0 or Checks.Check0And1 && fn.ReadsDoubleStar) {
        resolver.reporter.Error(MessageSource.Resolver, expr.Origin,
          "a function declared with 'reads **' can only be used if applied to arguments");
      }

      // Check 1
      if (whichChecks == Checks.Check0And1 && ModuleDefinition.InSameSCC(context, fn)) {
        resolver.reporter.Error(MessageSource.Resolver, expr.Origin,
          "in the definition of a function, every recursive use of the function must apply it to arguments. Possible solution: eta expansion.");
      }
    }

    // Check 2
    if (whichChecks == Checks.Check2 && expr is FunctionCallExpr callExpr && ModuleDefinition.InSameSCC(context, callExpr.Function)) {
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
