using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

class ExtremeLemmaChecksVisitor : ResolverBottomUpVisitor {
  ExtremeLemma context;
  public ExtremeLemmaChecksVisitor(ModuleResolver resolver, ExtremeLemma context)
    : base(resolver) {
    Contract.Requires(resolver != null);
    Contract.Requires(context != null);
    this.context = context;
  }
  protected override void VisitOneStmt(Statement stmt) {
    if (stmt is CallStmt callStmt) {
      if (callStmt.Method is ExtremeLemma or PrefixLemma) {
        // all is cool
      } else {
        // the call goes from an extreme lemma context to a non-extreme-lemma callee
        if (ModuleDefinition.InSameSCC(context, callStmt.Method)) {
          // we're looking at a recursive call (to a non-extreme-lemma)
          resolver.reporter.Error(MessageSource.Resolver, callStmt.Origin, "a recursive call from a {0} can go only to other {0}s and prefix lemmas", context.WhatKind);
        }
      }
    }
  }
  protected override void VisitOneExpr(Expression expr) {
    if (expr is FunctionCallExpr callExpr) {
      // the call goes from a greatest lemma context to a non-greatest-lemma callee
      if (ModuleDefinition.InSameSCC(context, callExpr.Function)) {
        // we're looking at a recursive call (to a non-greatest-lemma)
        resolver.reporter.Error(MessageSource.Resolver, callExpr.Origin, "a recursive call from a greatest lemma can go only to other greatest lemmas and prefix lemmas");
      }
    }
  }
}