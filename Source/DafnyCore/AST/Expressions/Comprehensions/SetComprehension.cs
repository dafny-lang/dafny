using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class SetComprehension : ComprehensionExpr, ICloneable<SetComprehension> {
  public override string WhatKind => "set comprehension";

  public readonly bool Finite;
  public readonly bool TermIsImplicit;  // records the given syntactic form
  public bool TermIsSimple {
    get {
      var term = Term as IdentifierExpr;
      var r = term != null && BoundVars.Count == 1 && BoundVars[0].Name == term.Name;
      Contract.Assert(!TermIsImplicit || r);  // TermIsImplicit ==> r
      Contract.Assert(!r || term.Var == null || term.Var == BoundVars[0]);  // if the term is simple and it has been resolved, then it should have resolved to BoundVars[0]
      return r;
    }
  }

  public SetComprehension Clone(Cloner cloner) {
    return new SetComprehension(cloner, this);
  }

  public SetComprehension(Cloner cloner, SetComprehension original) : base(cloner, original) {
    TermIsImplicit = original.TermIsImplicit;
    Finite = original.Finite;
  }

  public SetComprehension(IOrigin tok, IOrigin rangeOrigin, bool finite, List<BoundVar> bvars, Expression range, Expression/*?*/ term, Attributes attrs)
    : base(tok, rangeOrigin, bvars, range, term ?? new IdentifierExpr(tok, bvars[0].Name), attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(bvars));
    Contract.Requires(1 <= bvars.Count);
    Contract.Requires(range != null);
    Contract.Requires(term != null || bvars.Count == 1);

    TermIsImplicit = term == null;
    Finite = finite;
  }
}