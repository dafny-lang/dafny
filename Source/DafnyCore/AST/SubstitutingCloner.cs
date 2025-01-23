using System.Collections.Generic;

namespace Microsoft.Dafny;

class SubstitutingCloner(Dictionary<IVariable, IVariable> substitutions, bool cloneResolvedFields)
  : Cloner(false, cloneResolvedFields) {
  public override Expression CloneExpr(Expression expr) {
    if (expr is IdentifierExpr identifierExpr) {
      if (substitutions.TryGetValue(identifierExpr.Var, out var variableReplacement)) {
        // TODO consider using the code from Substituter
        return new IdentifierExpr(expr.Origin, variableReplacement);
      }
    }

    return base.CloneExpr(expr);
  }
}