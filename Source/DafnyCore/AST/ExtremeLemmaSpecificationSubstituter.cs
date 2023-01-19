using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// The ExtremeLemmaSpecificationSubstituter clones the precondition (or postcondition) declared
/// on a least (resp. greatest) lemma, but replaces the calls and equalities in "coConclusions"
/// with corresponding prefix versions.  The resulting expression is then appropriate to be a
/// precondition (resp. postcondition) of the least (resp. greatest) lemma's corresponding prefix lemma.
/// It is assumed that the source expression has been resolved.  Note, the "k" given to the constructor
/// is not cloned with each use; it is simply used as is.
/// The resulting expression needs to be resolved by the caller.
/// </summary>
class ExtremeLemmaSpecificationSubstituter : ExtremeCloner {
  readonly bool isCoContext;
  readonly ISet<Expression> friendlyCalls;
  public ExtremeLemmaSpecificationSubstituter(ISet<Expression> friendlyCalls, Expression k, ErrorReporter reporter, bool isCoContext)
    : base(k, reporter) {
    Contract.Requires(friendlyCalls != null);
    Contract.Requires(k != null);
    Contract.Requires(reporter != null);
    this.isCoContext = isCoContext;
    this.friendlyCalls = friendlyCalls;
  }
  public override Expression CloneExpr(Expression expr) {
    if (expr is NameSegment || expr is ExprDotName) {
      // make sure to clone any user-supplied type-parameter instantiations
      return base.CloneExpr(expr);
    } else if (expr is ApplySuffix) {
      var e = (ApplySuffix)expr;
      var r = e.Resolved as FunctionCallExpr;
      if (r != null && friendlyCalls.Contains(r)) {
        return CloneCallAndAddK(e);
      }
    } else if (expr is SuffixExpr) {
      // make sure to clone any user-supplied type-parameter instantiations
      return base.CloneExpr(expr);
    } else if (expr is ConcreteSyntaxExpression) {
      var e = (ConcreteSyntaxExpression)expr;
      // Note, the ExtremeLemmaSpecificationSubstituter is an unusual cloner in that it operates on
      // resolved expressions.  Hence, we bypass the syntactic parts here, except for the ones
      // checked above.
      return CloneExpr(e.Resolved);
    } else if (expr is FunctionCallExpr) {
      var e = (FunctionCallExpr)expr;
      if (friendlyCalls.Contains(e)) {
        return CloneCallAndAddK(e);
      }
    } else if (expr is BinaryExpr && isCoContext) {
      var e = (BinaryExpr)expr;
      if ((e.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || e.ResolvedOp == BinaryExpr.ResolvedOpcode.NeqCommon) && friendlyCalls.Contains(e)) {
        var op = e.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon ? TernaryExpr.Opcode.PrefixEqOp : TernaryExpr.Opcode.PrefixNeqOp;
        var A = CloneExpr(e.E0);
        var B = CloneExpr(e.E1);
        var teq = new TernaryExpr(Tok(e.tok), op, k, A, B);
        var opString = op == TernaryExpr.Opcode.PrefixEqOp ? "==" : "!=";
        reporter.Info(MessageSource.Cloner, e.tok, opString + suffix);
        return teq;
      }
    }
    return base.CloneExpr(expr);
  }
  public override Type CloneType(Type t) {
    if (t is UserDefinedType) {
      var tt = (UserDefinedType)t;
      // We want syntactic cloning of the Expression that is tt.NamePath, unlike the semantic (that is, post-resolved)
      // cloning that CloneExpr is doing above.
      return new UserDefinedType(Tok(tt.RangeToken), CloneNamePathExpression(tt.NamePath));
    } else {
      return base.CloneType(t);
    }
  }
  Expression CloneNamePathExpression(Expression expr) {
    Contract.Requires(expr is NameSegment || expr is ExprDotName);
    if (expr is NameSegment) {
      var e = (NameSegment)expr;
      return new NameSegment(this, e);
    } else {
      var e = (ExprDotName)expr;
      return new ExprDotName(Tok(e.RangeToken), CloneNamePathExpression(e.Lhs), e.SuffixName, e.OptTypeArguments == null ? null : e.OptTypeArguments.ConvertAll(CloneType));
    }
  }
}
