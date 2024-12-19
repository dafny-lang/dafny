using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

class ExtremeLemmaChecks_Visitor : ResolverBottomUpVisitor {
  ExtremeLemma context;
  public ExtremeLemmaChecks_Visitor(ModuleResolver resolver, ExtremeLemma context)
    : base(resolver) {
    Contract.Requires(resolver != null);
    Contract.Requires(context != null);
    this.context = context;
  }
  protected override void VisitOneStmt(Statement stmt) {
    if (stmt is CallStmt) {
      var s = (CallStmt)stmt;
      if (s.Method is ExtremeLemma || s.Method is PrefixLemma) {
        // all is cool
      } else {
        // the call goes from an extreme lemma context to a non-extreme-lemma callee
        if (ModuleDefinition.InSameSCC(context, s.Method)) {
          // we're looking at a recursive call (to a non-extreme-lemma)
          resolver.reporter.Error(MessageSource.Resolver, s.Tok, "a recursive call from a {0} can go only to other {0}s and prefix lemmas", context.WhatKind);
        }
      }
    }
  }
  protected override void VisitOneExpr(Expression expr) {
    if (expr is FunctionCallExpr) {
      var e = (FunctionCallExpr)expr;
      // the call goes from a greatest lemma context to a non-greatest-lemma callee
      if (ModuleDefinition.InSameSCC(context, e.Function)) {
        // we're looking at a recursive call (to a non-greatest-lemma)
        resolver.reporter.Error(MessageSource.Resolver, e.Tok, "a recursive call from a greatest lemma can go only to other greatest lemmas and prefix lemmas");
      }
    }
  }
}