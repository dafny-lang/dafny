using System.Collections.Generic;

namespace Microsoft.Dafny {
  public class FunctionCallSubstituter : Substituter {
    public readonly Function A, B;
    public FunctionCallSubstituter(Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Function a, Function b)
      : base(receiverReplacement, substMap, new Dictionary<TypeParameter, Type>()) {
      A = a;
      B = b;
    }
    public override Expression Substitute(Expression expr) {
      if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        Expression receiver = Substitute(e.Receiver);
        List<Expression> newArgs = SubstituteExprList(e.Args);
        FunctionCallExpr newFce = new FunctionCallExpr(expr.RangeToken, e.Name, receiver, newArgs, e.AtLabel);
        if (e.Function == A) {
          newFce.Function = B;
          newFce.Type = e.Type; // TODO: this may not work with type parameters.
        } else {
          newFce.Function = e.Function;
          newFce.Type = e.Type;
        }
        newFce.TypeApplication_AtEnclosingClass = e.TypeApplication_AtEnclosingClass;  // resolve here
        newFce.TypeApplication_JustFunction = e.TypeApplication_JustFunction;  // resolve here
        newFce.IsByMethodCall = e.IsByMethodCall;
        return newFce;
      }
      return base.Substitute(expr);
    }
  }
}