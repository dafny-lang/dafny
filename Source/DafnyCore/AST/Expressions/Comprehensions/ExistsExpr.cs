#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ExistsExpr : QuantifierExpr, ICloneable<ExistsExpr> {
  public override string WhatKind => "exists expression";
  protected override BinaryExpr.ResolvedOpcode SplitResolvedOp => BinaryExpr.ResolvedOpcode.Or;

  [SyntaxConstructor]
  public ExistsExpr(IOrigin origin, List<BoundVar> boundVars, Expression? range, Expression term, Attributes? attributes = null)
    : base(origin, boundVars, range, term, attributes) {
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
    var body = new BinaryExpr(Term.Origin, BinaryExpr.Opcode.And, Range, Term);
    body.ResolvedOp = BinaryExpr.ResolvedOpcode.And;
    body.Type = Term.Type;
    return body;
  }

  /// <summary>
  /// Returns an expression like 'exists' but where the bound variables have been renamed to have
  /// 'prefix' as a prefix to their previous names.
  /// Assumes the expression has been resolved.
  /// </summary>
  public Expression AlphaRename(string prefix) {
    if (SplitQuantifierExpression is ExistsExpr splitQuantifierExpression) {
      return splitQuantifierExpression.AlphaRename(prefix);
    }

    var substMap = new Dictionary<IVariable, Expression>();
    var bvars = new List<BoundVar>();
    foreach (var bv in BoundVars) {
      var newBv = new BoundVar(bv.Origin, prefix + bv.Name, bv.Type);
      bvars.Add(newBv);
      var ie = new IdentifierExpr(newBv.Origin, newBv);
      substMap.Add(bv, ie);
    }
    var s = new Substituter(null, substMap, new Dictionary<TypeParameter, Type>());
    var range = Range == null ? null : s.Substitute(Range);
    var term = s.Substitute(Term);
    var attrs = s.SubstAttributes(Attributes);

    var ex = new ExistsExpr(Origin, bvars, range, term, attrs) {
      Type = Type.Bool,
      Bounds = s.SubstituteBoundedPoolList(Bounds),
    };
    return ex;
  }
}
