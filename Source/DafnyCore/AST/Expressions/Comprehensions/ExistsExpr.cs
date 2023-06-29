using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ExistsExpr : QuantifierExpr, ICloneable<ExistsExpr> {
  public override string WhatKind => "exists expression";
  protected override BinaryExpr.ResolvedOpcode SplitResolvedOp { get { return BinaryExpr.ResolvedOpcode.Or; } }

  public ExistsExpr(IToken tok, RangeToken rangeToken, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
    : base(tok, rangeToken, bvars, range, term, attrs) {
    Contract.Requires(cce.NonNullElements(bvars));
    Contract.Requires(tok != null);
    Contract.Requires(term != null);
  }

  public ExistsExpr Clone(Cloner cloner) {
    return new ExistsExpr(cloner, this);
  }

  public ExistsExpr(Cloner cloner, ExistsExpr existsExpr) : base(cloner, existsExpr) {
  }

  public override Expression LogicalBody(bool bypassSplitQuantifier = false) {
    if (Range == null) {
      return Term;
    }
    var body = new BinaryExpr(Term.tok, BinaryExpr.Opcode.And, Range, Term);
    body.ResolvedOp = BinaryExpr.ResolvedOpcode.And;
    body.Type = Term.Type;
    return body;
  }
}