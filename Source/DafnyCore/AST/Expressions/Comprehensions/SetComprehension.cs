#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class SetComprehension : ComprehensionExpr, ICloneable<SetComprehension> {
  public override string WhatKind => "set comprehension";

  public bool Finite;
  public bool TermIsImplicit;  // records the given syntactic form
  public bool TermIsSimple {
    get {
      var term = Term as IdentifierExpr;
      var r = term != null && BoundVars.Count == 1 && BoundVars[0].Name == term.Name;
      Contract.Assert(!TermIsImplicit || r);  // TermIsImplicit ==> r
      Contract.Assert(!r || term!.Var == null || term.Var == BoundVars[0]);  // if the term is simple and it has been resolved, then it should have resolved to BoundVars[0]
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

  [SyntaxConstructor]
  public SetComprehension(IOrigin origin, bool finite, List<BoundVar> boundVars, Expression range, Expression? term, Attributes? attributes = null)
    : base(origin, boundVars, range, term ?? new IdentifierExpr(origin, boundVars[0].Name), attributes) {
    Contract.Requires(1 <= boundVars.Count);
    Contract.Requires(term != null || boundVars.Count == 1);

    TermIsImplicit = term == null;
    Finite = finite;
  }
}