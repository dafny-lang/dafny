using System.Collections.Generic;

namespace Microsoft.Dafny {
  public class FunctionCallSubstituter : Substituter {
    public readonly Function A, B;
    public FunctionCallSubstituter(Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Dictionary<TypeParameter, Type> typeMap, Function a, Function b)
      : base(receiverReplacement, substMap, typeMap) {
      A = a;
      B = b;
    }
    public override Expression Substitute(Expression expr) {
      if (expr is FunctionCallExpr e) {
        var receiver = Substitute(e.Receiver);
        var newArgs = SubstituteExprList(e.Args);
        var newFce = new FunctionCallExpr(e.tok, e.Name, receiver, e.OpenParen, e.CloseParen, newArgs, e.AtLabel);
        if (e.Function == A && e.Receiver is ThisExpr && receiver is ThisExpr) {
          newFce.Function = B;
          newFce.Type = e.Type; // TODO: this may not work with type parameters.
                                //update receiver type
          receiver.Type = Resolver.GetThisType(B.tok, (TopLevelDeclWithMembers)B.EnclosingClass);
        } else {
          newFce.Function = e.Function;
          newFce.Type = e.Type;
        }
        newFce.TypeApplication_AtEnclosingClass = SubstituteTypeList(e.TypeApplication_AtEnclosingClass);  // resolve here
        newFce.TypeApplication_JustFunction = SubstituteTypeList(e.TypeApplication_JustFunction);  // resolve here
        newFce.IsByMethodCall = e.IsByMethodCall;
        return newFce;
      }
      return base.Substitute(expr);
    }
  }
}