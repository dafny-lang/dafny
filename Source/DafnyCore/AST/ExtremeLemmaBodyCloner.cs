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
  readonly ISet<CoDatatypeDecl> focalCodatatypeEquality;
  public ExtremeLemmaBodyCloner(ExtremeLemma context, Expression k,
    ISet<ExtremePredicate> focalPredicates, ISet<CoDatatypeDecl> focalCodatatypeEquality, ErrorReporter reporter)
    : base(k, reporter) {
    Contract.Requires(context != null);
    Contract.Requires(k != null);
    Contract.Requires(reporter != null);
    this.context = context;
    this.focalPredicates = focalPredicates;
    this.focalCodatatypeEquality = focalCodatatypeEquality;
  }

  public override Expression CloneExpr(Expression expr) {
    if (reporter.Options.RewriteFocalPredicates) {
      if (expr is FunctionCallExpr functionCallExpr) {
        // Note, we don't actually ever get here, because all calls will have been parsed as ApplySuffix.
        // However, if something changes in the future (for example, some rewrite that changing an ApplySuffix
        // to its resolved FunctionCallExpr), then we do want this code, so with the hope of preventing
        // some error in the future, this case is included.  (Of course, it is currently completely untested!)
        if (functionCallExpr.Function is ExtremePredicate f && focalPredicates.Contains(f)) {
          return CloneCallAndAddK(functionCallExpr);
        }
      } else if (expr is StaticReceiverExpr ee) {
        return new StaticReceiverExpr(Origin(ee.Origin), ee.Type, ee.IsImplicit);
      } else if (expr is ApplySuffix apply) {
        if (!apply.WasResolved()) {
          // Since we're assuming the enclosing statement to have been resolved, this ApplySuffix must
          // be part of an ExprRhs that actually designates a method call.  Such an ApplySuffix does
          // not get listed as being resolved, but its components (like its .Lhs) are resolved.
          var mse = (MemberSelectExpr)apply.Lhs.Resolved;
          Contract.Assume(mse.Member is Method);
        } else {
          if (apply.Resolved is FunctionCallExpr fce) {
            if (fce.Function is ExtremePredicate f && focalPredicates.Contains(f)) {
              return CloneCallAndAddK(fce);
            }
          }
        }
      } else if (expr is BinaryExpr { ResolvedOp: BinaryExpr.ResolvedOpcode.EqCommon or BinaryExpr.ResolvedOpcode.NeqCommon } binaryExpr) {
        if (binaryExpr.E0.Type.AsCoDatatype is { } coDatatypeDecl && focalCodatatypeEquality.Contains(coDatatypeDecl)) {
          return CloneEqualityAndAddK(binaryExpr);
        }
      }
    }
    return base.CloneExpr(expr);
  }
  public override AssignmentRhs CloneRHS(AssignmentRhs rhs) {
    if (rhs is ExprRhs { Expr: ApplySuffix apply }) {
      if (apply.Lhs.Resolved is MemberSelectExpr { Member: ExtremeLemma extremeLemma } && ModuleDefinition.InSameSCC(context, extremeLemma)) {
        // we're looking at a recursive call to an extreme lemma
        Contract.Assert(apply.Lhs is NameSegment or ExprDotName); // this is the only way a call statement can have been parsed
        // clone "apply.Lhs", changing the least/greatest lemma to the prefix lemma; then clone "apply", adding in the extra argument
        Expression lhsClone;
        if (apply.Lhs is NameSegment) {
          var lhs = (NameSegment)apply.Lhs;
          lhsClone = new NameSegment(Origin(lhs.Origin), lhs.Name + "#", lhs.OptTypeArguments?.ConvertAll(CloneType));
        } else {
          var lhs = (ExprDotName)apply.Lhs;
          lhsClone = new ExprDotName(Origin(lhs.Origin), CloneExpr(lhs.Lhs), lhs.SuffixNameNode.Append("#"), lhs.OptTypeArguments?.ConvertAll(CloneType));
        }

        var args = new List<ActualBinding>();
        args.Add(new ActualBinding(null, k));
        apply.Bindings.ArgumentBindings.ForEach(arg => args.Add(CloneActualBinding(arg)));
        var applyClone = new ApplySuffix(Origin(apply.Origin), apply.AtTok == null ? null : Origin(apply.AtTok),
          lhsClone, args, apply.CloseParen);
        var c = new ExprRhs(applyClone, CloneAttributes(rhs.Attributes));
        reporter.Info(MessageSource.Cloner, apply.Lhs.Origin, extremeLemma.Name + suffix);
        return c;
      }
    }

    return base.CloneRHS(rhs);
  }
}
