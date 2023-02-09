using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny {
  public class FunctionCallSubstituter : Substituter {
    public readonly TraitDecl Tr;
    public readonly ClassDecl Cl;
    public readonly List<Function> whitelist;

    public FunctionCallSubstituter(Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Dictionary<TypeParameter, Type> typeMap, Function f)
      : base(null, substMap, typeMap) {
      var tf = f.OverriddenFunction;
      Tr = (TraitDecl)tf.EnclosingClass;
      Cl = (ClassDecl)f.EnclosingClass;
      whitelist = tf.EnclosingClass.EnclosingModuleDefinition.CallGraph.GetSCC(tf).OfType<Function>().ToList();
    }
    public override Expression Substitute(Expression expr) {
      if (expr is FunctionCallExpr e) {
        var receiver = Substitute(e.Receiver);
        var newArgs = SubstituteExprList(e.Args);
        Function function;
        if (e.Function.EnclosingClass == Tr && e.Receiver is ThisExpr && receiver is ThisExpr && whitelist.Contains(e.Function) && Cl.Members.Find(m => m.OverriddenMember == e.Function) is { } f) {
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