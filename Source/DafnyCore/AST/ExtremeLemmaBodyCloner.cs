using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// The task of the ExtremeLemmaBodyCloner is to fill in the implicit _k-1 arguments in recursive least/greatest lemma calls
/// and in calls to the focal predicates.
/// The source statement and the given "k" are assumed to have been resolved.
/// </summary>
class ExtremeLemmaBodyCloner : ExtremeCloner {
  readonly ExtremeLemma context;
  readonly ISet<ExtremePredicate> focalPredicates;
  public ExtremeLemmaBodyCloner(ExtremeLemma context, Expression k, ISet<ExtremePredicate> focalPredicates, ErrorReporter reporter)
    : base(k, reporter) {
    Contract.Requires(context != null);
    Contract.Requires(k != null);
    Contract.Requires(reporter != null);
    this.context = context;
    this.focalPredicates = focalPredicates;
  }

  public override Expression CloneExpr(Expression expr) {
    if (reporter.Options.RewriteFocalPredicates) {
      if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
#if DEBUG_PRINT
          if (e.Function.Name.EndsWith("#") && Contract.Exists(focalPredicates, p => e.Function.Name == p.Name + "#")) {
            Console.WriteLine("{0}({1},{2}): DEBUG: Possible opportunity to rely on new rewrite: {3}", e.tok.filename, e.tok.line, e.tok.col, Printer.ExprToString(e));
          }
#endif
        // Note, we don't actually ever get here, because all calls will have been parsed as ApplySuffix.
        // However, if something changes in the future (for example, some rewrite that changing an ApplySuffix
        // to its resolved FunctionCallExpr), then we do want this code, so with the hope of preventing
        // some error in the future, this case is included.  (Of course, it is currently completely untested!)
        var f = e.Function as ExtremePredicate;
        if (f != null && focalPredicates.Contains(f)) {
#if DEBUG_PRINT
            var r = CloneCallAndAddK(e);
            Console.WriteLine("{0}({1},{2}): DEBUG: Rewrote extreme predicate into prefix predicate: {3}", e.tok.filename, e.tok.line, e.tok.col, Printer.ExprToString(r));
            return r;
#else
          return CloneCallAndAddK(e);
#endif
        }
      } else if (expr is StaticReceiverExpr ee) {
        return new StaticReceiverExpr(Tok(ee.tok), ee.Type, ee.IsImplicit);
      } else if (expr is ApplySuffix) {
        var apply = (ApplySuffix)expr;
        if (!apply.WasResolved()) {
          // Since we're assuming the enclosing statement to have been resolved, this ApplySuffix must
          // be part of an ExprRhs that actually designates a method call.  Such an ApplySuffix does
          // not get listed as being resolved, but its components (like its .Lhs) are resolved.
          var mse = (MemberSelectExpr)apply.Lhs.Resolved;
          Contract.Assume(mse.Member is Method);
        } else {
          var fce = apply.Resolved as FunctionCallExpr;
          if (fce != null) {
#if DEBUG_PRINT
              if (fce.Function.Name.EndsWith("#") && Contract.Exists(focalPredicates, p => fce.Function.Name == p.Name + "#")) {
                Console.WriteLine("{0}({1},{2}): DEBUG: Possible opportunity to rely on new rewrite: {3}", fce.tok.filename, fce.tok.line, fce.tok.col, Printer.ExprToString(fce));
              }
#endif
            var f = fce.Function as ExtremePredicate;
            if (f != null && focalPredicates.Contains(f)) {
#if DEBUG_PRINT
                var r = CloneCallAndAddK(fce);
                Console.WriteLine("{0}({1},{2}): DEBUG: Rewrote extreme predicate into prefix predicate: {3}", fce.tok.filename, fce.tok.line, fce.tok.col, Printer.ExprToString(r));
                return r;
#else
              return CloneCallAndAddK(fce);
#endif
            }
          }
        }
      }
    }
    return base.CloneExpr(expr);
  }
  public override AssignmentRhs CloneRHS(AssignmentRhs rhs) {
    var r = rhs as ExprRhs;
    if (r != null && r.Expr is ApplySuffix) {
      var apply = (ApplySuffix)r.Expr;
      var mse = apply.Lhs.Resolved as MemberSelectExpr;
      if (mse != null && mse.Member is ExtremeLemma && ModuleDefinition.InSameSCC(context, (ExtremeLemma)mse.Member)) {
        // we're looking at a recursive call to an extreme lemma
        Contract.Assert(apply.Lhs is NameSegment || apply.Lhs is ExprDotName);  // this is the only way a call statement can have been parsed
        // clone "apply.Lhs", changing the least/greatest lemma to the prefix lemma; then clone "apply", adding in the extra argument
        Expression lhsClone;
        if (apply.Lhs is NameSegment) {
          var lhs = (NameSegment)apply.Lhs;
          lhsClone = new NameSegment(Tok(lhs.tok), lhs.Name + "#", lhs.OptTypeArguments == null ? null : lhs.OptTypeArguments.ConvertAll(CloneType));
        } else {
          var lhs = (ExprDotName)apply.Lhs;
          lhsClone = new ExprDotName(Tok(lhs.tok), CloneExpr(lhs.Lhs), lhs.SuffixName + "#", lhs.OptTypeArguments == null ? null : lhs.OptTypeArguments.ConvertAll(CloneType));
        }
        var args = new List<ActualBinding>();
        args.Add(new ActualBinding(null, k));
        apply.Bindings.ArgumentBindings.ForEach(arg => args.Add(CloneActualBinding(arg)));
        var applyClone = new ApplySuffix(Tok(apply.tok), apply.AtTok == null ? null : Tok(apply.AtTok),
          lhsClone, args, Tok(apply.CloseParen));
        var c = new ExprRhs(applyClone, CloneAttributes(rhs.Attributes));
        reporter.Info(MessageSource.Cloner, apply.Lhs.tok, mse.Member.Name + suffix);
        return c;
      }
    }
    return base.CloneRHS(rhs);
  }
}
