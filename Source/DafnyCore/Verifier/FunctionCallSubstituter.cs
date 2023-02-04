using System.Collections.Generic;

namespace Microsoft.Dafny {
  public class FunctionCallSubstituter : Substituter {
    public readonly TraitDecl Tr;
    public readonly ClassDecl Cl;

    public FunctionCallSubstituter(Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Dictionary<TypeParameter, Type> typeMap, TraitDecl Tr, ClassDecl Cl)
      : base(null, substMap, typeMap) {
      this.Tr = Tr;
      this.Cl = Cl;
    }
    public override Expression Substitute(Expression expr) {
      if (expr is FunctionCallExpr e) {
        var receiver = Substitute(e.Receiver);
        var newArgs = SubstituteExprList(e.Args);
        var newFce = new FunctionCallExpr(e.tok, e.Name, receiver, e.OpenParen, e.CloseParen, newArgs, e.AtLabel);
        if (e.Function.EnclosingClass == Tr && e.Receiver is ThisExpr && receiver is ThisExpr && Cl.Members.Find(m => m.OverriddenMember == e.Function) is { } f) {
          newFce.Function = (Function)f;
          newFce.Type = e.Type; // TODO: this may not work with type parameters.
          receiver = new ThisExpr((TopLevelDeclWithMembers)f.EnclosingClass);
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