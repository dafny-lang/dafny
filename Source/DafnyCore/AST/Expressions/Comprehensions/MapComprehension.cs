using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class MapComprehension : ComprehensionExpr, ICloneable<MapComprehension> {
  public override string WhatKind => "map comprehension";

  public readonly bool Finite;
  public readonly Expression TermLeft;

  public List<Boogie.Function> ProjectionFunctions;  // filled in during translation (and only for general map comprehensions where "TermLeft != null")

  public MapComprehension Clone(Cloner cloner) {
    return new MapComprehension(cloner, this);
  }

  public MapComprehension(Cloner cloner, MapComprehension original) : base(cloner, original) {
    TermLeft = cloner.CloneExpr(original.TermLeft);
    Finite = original.Finite;
  }

  public MapComprehension(IOrigin tok, IOrigin rangeOrigin, bool finite, List<BoundVar> bvars, Expression range, Expression/*?*/ termLeft, Expression termRight, Attributes attrs)
    : base(tok, rangeOrigin, bvars, range, termRight, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(bvars));
    Contract.Requires(1 <= bvars.Count);
    Contract.Requires(range != null);
    Contract.Requires(termRight != null);
    Contract.Requires(termLeft != null || bvars.Count == 1);

    Finite = finite;
    TermLeft = termLeft;
  }

  /// <summary>
  /// IsGeneralMapComprehension returns true for general map comprehensions.
  /// In other words, it returns false if either no TermLeft was given or if
  /// the given TermLeft is the sole bound variable.
  /// This property getter requires that the expression has been successfully
  /// resolved.
  /// </summary>
  public bool IsGeneralMapComprehension {
    get {
      Contract.Requires(WasResolved());
      if (TermLeft == null) {
        return false;
      } else if (BoundVars.Count != 1) {
        return true;
      }
      var lhs = StripParens(TermLeft).Resolved;
      if (lhs is IdentifierExpr ide && ide.Var == BoundVars[0]) {
        // TermLeft is the sole bound variable, so this is the same as
        // if TermLeft wasn't given at all
        return false;
      }
      return true;
    }
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var e in Attributes.SubExpressions(Attributes)) {
        yield return e;
      }
      if (Range != null) { yield return Range; }
      if (TermLeft != null) { yield return TermLeft; }
      yield return Term;
    }
  }
}