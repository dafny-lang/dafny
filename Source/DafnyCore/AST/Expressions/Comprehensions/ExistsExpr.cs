using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ExistsExpr : QuantifierExpr, ICloneable<ExistsExpr> {
  public override string WhatKind => "exists expression";
  protected override BinaryExpr.ResolvedOpcode SplitResolvedOp { get { return BinaryExpr.ResolvedOpcode.Or; } }

  public ExistsExpr(IOrigin tok, IOrigin rangeOrigin, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
    : base(tok, rangeOrigin, bvars, range, term, attrs) {
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
    var body = new BinaryExpr(Term.Tok, BinaryExpr.Opcode.And, Range, Term);
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
    Contract.Requires(this != null);
    Contract.Requires(prefix != null);

    if (SplitQuantifier != null) {
      // TODO: what to do?  Substitute(exists.SplitQuantifierExpression);
    }

    var substMap = new Dictionary<IVariable, Expression>();
    var var4var = new Dictionary<BoundVar, BoundVar>();
    var bvars = new List<BoundVar>();
    foreach (var bv in BoundVars) {
      var newBv = new BoundVar(bv.Tok, prefix + bv.Name, bv.Type);
      bvars.Add(newBv);
      var4var.Add(bv, newBv);
      var ie = new IdentifierExpr(newBv.Tok, newBv.Name);
      ie.Var = newBv;  // resolve here
      ie.Type = newBv.Type;  // resolve here
      substMap.Add(bv, ie);
    }
    var s = new Substituter(null, substMap, new Dictionary<TypeParameter, Type>());
    var range = Range == null ? null : s.Substitute(Range);
    var term = s.Substitute(Term);
    var attrs = s.SubstAttributes(Attributes);
    var ex = new ExistsExpr(Tok, Origin, bvars, range, term, attrs);
    ex.Type = Type.Bool;
    ex.Bounds = s.SubstituteBoundedPoolList(Bounds);
    return ex;
  }
}