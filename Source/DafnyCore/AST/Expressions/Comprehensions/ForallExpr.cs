using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ForallExpr : QuantifierExpr, ICloneable<ForallExpr> {
  public override string WhatKind => "forall expression";
  protected override BinaryExpr.ResolvedOpcode SplitResolvedOp => BinaryExpr.ResolvedOpcode.And;

  public ForallExpr(IOrigin tok, IOrigin rangeOrigin, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
    : base(tok, rangeOrigin, bvars, range, term, attrs) {
    Contract.Requires(cce.NonNullElements(bvars));
    Contract.Requires(tok != null);
    Contract.Requires(term != null);
  }

  public ForallExpr Clone(Cloner cloner) {
    return new ForallExpr(cloner, this);
  }

  public ForallExpr(Cloner cloner, ForallExpr original) : base(cloner, original) {
  }

  public override Expression LogicalBody(bool bypassSplitQuantifier = false) {
    if (Range == null) {
      return Term;
    }
    var body = new BinaryExpr(Term.Tok, BinaryExpr.Opcode.Imp, Range, Term);
    body.ResolvedOp = BinaryExpr.ResolvedOpcode.Imp;
    body.Type = Term.Type;
    return body;
  }
}