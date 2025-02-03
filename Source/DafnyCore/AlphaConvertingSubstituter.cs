using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  /// <summary>
  /// This substituter performs substitutions in such a way that it's okay to print the resulting expression without a human getting confused.
  /// More precisely, bound variables first gets alpha-renamed.  Also, "this" is never left implicit, including in the
  /// case where "receiverReplacement" is given as ImplicitThisExpr (but no attempt is made to substitute for all ImplicitThisExpr's in
  /// "receiverReplacement" and the range of "substMap").
  /// </summary>
  public class AlphaConvertingSubstituter : Substituter {
    public AlphaConvertingSubstituter(Expression receiverReplacement, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap)
      : base(receiverReplacement is ImplicitThisExpr ? new ThisExpr(receiverReplacement.Origin) { Type = receiverReplacement.Type } : receiverReplacement, substMap, typeMap) {
      Contract.Requires(substMap != null);
      Contract.Requires(typeMap != null);
    }
    protected override List<BoundVar> CreateBoundVarSubstitutions(List<BoundVar> vars, bool forceSubstitutionOfBoundVars) {
      var newBoundVars = vars.Count == 0 ? vars : [];
      foreach (var bv in vars) {
        var tt = bv.Type.Subst(typeMap);
        var newBv = new BoundVar(bv.Origin, "_'" + bv.Name, tt);
        newBoundVars.Add(newBv);
        // update substMap to reflect the new BoundVar substitutions
        var ie = new IdentifierExpr(newBv.Origin, newBv.Name) { Var = newBv, Type = newBv.Type };
        substMap.Add(bv, ie);
      }
      return newBoundVars;
    }
  }
}