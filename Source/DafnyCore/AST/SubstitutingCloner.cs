using System.Collections.Generic;

namespace Microsoft.Dafny;

class SubstitutingCloner : Cloner {
  private readonly Dictionary<IVariable, IVariable> substitutions;

  public SubstitutingCloner(Dictionary<IVariable, IVariable> substitutions, bool cloneResolvedFields)
    : base(false, cloneResolvedFields) {
    this.substitutions = substitutions;
  }

  public override Expression CloneExpr(Expression expr) {
    if (expr is IdentifierExpr identifierExpr) {
      if (substitutions.TryGetValue(identifierExpr.Var, out var variableReplacement)) {
        // TODO consider using the code from Substituter
        return new IdentifierExpr(expr.Tok, variableReplacement);
      }
    }

    return base.CloneExpr(expr);
  }
}