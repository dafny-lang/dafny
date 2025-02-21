using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  public class PrefixCallSubstituter : Substituter {
    readonly ExtremePredicate extremePred;
    readonly Expression unrollDepth;
    readonly ModuleDefinition module;
    public PrefixCallSubstituter(Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Dictionary<TypeParameter, Type> tySubstMap, ExtremePredicate extremePredicate, Expression depth)
      : base(receiverReplacement, substMap, tySubstMap) {
      Contract.Requires(extremePredicate != null);
      Contract.Requires(depth != null);
      extremePred = extremePredicate;
      unrollDepth = depth;
      module = extremePredicate.EnclosingClass.EnclosingModuleDefinition;
    }
    public override Expression Substitute(Expression expr) {
      if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        var cof = e.Function as ExtremePredicate;
        if (cof != null && ModuleDefinition.InSameSCC(cof, extremePred)) {
          expr = cof.CreatePrefixPredicateCall(e, unrollDepth);
        }
      }
      return base.Substitute(expr);
    }
  }
}