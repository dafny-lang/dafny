#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ForallExpr : QuantifierExpr, ICloneable<ForallExpr> {
  public override string WhatKind => "forall expression";
  protected override BinaryExpr.ResolvedOpcode SplitResolvedOp => BinaryExpr.ResolvedOpcode.And;

  [SyntaxConstructor]
  public ForallExpr(IOrigin origin, List<BoundVar> boundVars, Expression? range, Expression term, Attributes? attributes = null)
    : base(origin, boundVars, range, term, attributes) {
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
    var body = new BinaryExpr(Term.Origin, BinaryExpr.Opcode.Imp, Range, Term);
    body.ResolvedOp = BinaryExpr.ResolvedOpcode.Imp;
    body.Type = Term.Type;
    return body;
  }
}