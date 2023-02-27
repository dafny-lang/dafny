using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny {
  public class FunctionCallSubstituter : Substituter {
    public readonly TraitDecl Tr;
    public readonly ClassDecl Cl;

    // We replace all occurrences of the trait version of the function with the class version. This is only allowed if
    // the receiver is `this`. We underapproximate this by looking for a `ThisExpr`, which misses more complex
    // expressions that evaluate to one.
    public FunctionCallSubstituter(Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Dictionary<TypeParameter, Type> typeMap, TraitDecl Tr, ClassDecl Cl)
      : base(null, substMap, typeMap) {
      this.Tr = Tr;
      this.Cl = Cl;
    }

    public override Expression Substitute(Expression expr) {
      if (expr is FunctionCallExpr e) {
        var receiver = Substitute(e.Receiver);
        var newArgs = SubstituteExprList(e.Args);
        Function function;
        if ((e.Function.EnclosingClass == Tr || Tr.InheritedMembers.Contains(e.Function)) && e.Receiver is ThisExpr && receiver is ThisExpr && Cl.Members.Find(m => m.OverriddenMember == e.Function) is { } f) {
          receiver = new ThisExpr((TopLevelDeclWithMembers)f.EnclosingClass);
          function = (Function)f;
        } else {
          function = e.Function;
        }
        return new FunctionCallExpr(e.tok, e.Name, receiver, e.OpenParen, e.CloseParen, newArgs, e.AtLabel) {
          Function = function,
          Type = e.Type, // TODO: this may not work with type parameters.
          TypeApplication_AtEnclosingClass = SubstituteTypeList(e.TypeApplication_AtEnclosingClass), // resolve here
          TypeApplication_JustFunction = SubstituteTypeList(e.TypeApplication_JustFunction), // resolve here
          IsByMethodCall = e.IsByMethodCall
        };
      }
      return base.Substitute(expr);
    }
  }
}