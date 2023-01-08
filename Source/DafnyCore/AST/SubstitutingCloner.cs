using System.Collections.Generic;

namespace Microsoft.Dafny;

class SubstitutingCloner : Cloner {
  private readonly Dictionary<IVariable, Expression> substitutions;

  public SubstitutingCloner(Dictionary<IVariable, Expression> substitutions, bool cloneResolvedFields)
    : base(cloneResolvedFields) {
    this.substitutions = substitutions;
  }

  public override Expression CloneExpr(Expression expr) {
    if (expr is IdentifierExpr identifierExpr) {
      if (substitutions.TryGetValue(identifierExpr.Var, out var substitution)) {
        // TODO consider using the code from Substitutor
        return substitution;
      }
    }

    return base.CloneExpr(expr);
  }
}