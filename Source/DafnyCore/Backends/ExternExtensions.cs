using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public static class ExternExtensions {

  public static bool IsExtern(this IAttributeBearingDeclaration declaration, DafnyOptions options, out string/*?*/ qualification, out string/*?*/ name) {
    // ensures result==false ==> qualification == null && name == null
    Contract.Ensures(Contract.Result<bool>() || (Contract.ValueAtReturn(out qualification) == null && Contract.ValueAtReturn(out name) == null));
    // ensures result==true ==> qualification != null ==> name != null
    Contract.Ensures(!Contract.Result<bool>() || Contract.ValueAtReturn(out qualification) == null || Contract.ValueAtReturn(out name) != null);

    qualification = null;
    name = null;
    if (!options.DisallowExterns) {
      var externArgs = Attributes.FindExpressions(declaration.Attributes, "extern");
      if (externArgs != null) {
        if (externArgs.Count == 0) {
          return true;
        } else if (externArgs.Count == 1 && externArgs[0] is StringLiteralExpr) {
          name = externArgs[0].AsStringLiteral();
          return true;
        } else if (externArgs.Count == 2 && externArgs[0] is StringLiteralExpr && externArgs[1] is StringLiteralExpr) {
          qualification = externArgs[0].AsStringLiteral();
          name = externArgs[1].AsStringLiteral();
          return true;
        }
      }
    }
    return false;
  }
}