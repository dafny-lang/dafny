using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny {
  public class FunctionCallSubstituter : Substituter {
    public readonly TraitDecl Tr;
    public readonly TopLevelDeclWithMembers Impl;

    // We replace all occurrences of the trait version of the function with the class version. This is only allowed if
    // the receiver is `this`. We underapproximate this by looking for a `ThisExpr`, which misses more complex
    // expressions that evaluate to one.
    public FunctionCallSubstituter(Dictionary<IVariable, Expression /*!*/> /*!*/ substMap, Dictionary<TypeParameter, Type> typeMap,
      TraitDecl parentTrait, TopLevelDeclWithMembers impl)
      : base(new ThisExpr(impl.Tok) { Type = UserDefinedType.FromTopLevelDecl(impl.Tok, impl) }, substMap, typeMap) {
      Tr = parentTrait;
      Impl = impl;
    }

    public override Expression Substitute(Expression expr) {
      if (expr is FunctionCallExpr e) {
        var receiver = Substitute(e.Receiver);
        var newArgs = SubstituteExprList(e.Args);
        var typeApplicationAtEnclosingClass = e.TypeApplication_AtEnclosingClass;
        Function function;
        if ((e.Function.EnclosingClass == Tr || Tr.InheritedMembers.Contains(e.Function)) &&
            e.Receiver.Resolved is ThisExpr && receiver.Resolved is ThisExpr &&
            Impl.Members.Find(m => m.OverriddenMember == e.Function) is { } f) {
          receiver = new ThisExpr((TopLevelDeclWithMembers)f.EnclosingClass);
          function = (Function)f;
          typeApplicationAtEnclosingClass = receiver.Type.AsParentType(Impl).TypeArgs.ToList();
        } else {
          function = e.Function;
        }
        return new FunctionCallExpr(e.Tok, e.NameNode, receiver, e.OpenParen, e.CloseParen, newArgs, e.AtLabel) {
          Function = function,
          Type = e.Type.Subst(typeMap),
          TypeApplication_AtEnclosingClass = SubstituteTypeList(typeApplicationAtEnclosingClass), // resolve here
          TypeApplication_JustFunction = SubstituteTypeList(e.TypeApplication_JustFunction), // resolve here
          IsByMethodCall = e.IsByMethodCall
        };
      }
      return base.Substitute(expr);
    }
  }
}