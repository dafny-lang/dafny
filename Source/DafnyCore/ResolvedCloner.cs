namespace Microsoft.Dafny;


class ResolvedCloner : Cloner { // TODO delete.

  public override Type CloneType(Type t) {
    Type new_t = base.CloneType(t);

    if (t is UserDefinedType) {
      var tt = (UserDefinedType)t;
      var new_tt = (UserDefinedType)new_t;

      new_tt.ResolvedClass = tt.ResolvedClass;
    }

    return new_t;
  }

  public override CasePattern<VT> CloneCasePattern<VT>(CasePattern<VT> pat) {
    if (pat.Var != null) {
      var newPat = new CasePattern<VT>(pat.tok, CloneIVariable(pat.Var, false));
      newPat.AssembleExpr(null);
      return newPat;
    } else {
      var newArgs = pat.Arguments == null ? null : pat.Arguments.ConvertAll(CloneCasePattern);
      var patE = (DatatypeValue)pat.Expr;
      var newPat = new CasePattern<VT>(pat.tok, pat.Id, newArgs);
      newPat.Ctor = pat.Ctor;
      newPat.AssembleExpr(patE.InferredTypeArgs.ConvertAll(CloneType));
      return newPat;
    }
  }

  public override BoundVar CloneBoundVar(BoundVar bv, bool isReference) {
    // The difference here from the overridden method is that we do CloneType(bv.Type) instead of CloneType(bv.SyntacticType)
    var bvNew = new BoundVar(Tok(bv.tok), bv.Name, CloneType(bv.Type));
    bvNew.IsGhost = bv.IsGhost;
    return bvNew;
  }
}
