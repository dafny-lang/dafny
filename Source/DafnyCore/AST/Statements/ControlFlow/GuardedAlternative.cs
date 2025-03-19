using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class GuardedAlternative : NodeWithOrigin, IAttributeBearingDeclaration {
  public bool IsBindingGuard;
  public Expression Guard;
  public List<Statement> Body;
  public Attributes Attributes { get; set; }
  string IAttributeBearingDeclaration.WhatKind => "alternative-based case";
  public override IEnumerable<INode> Children => Attributes.AsEnumerable().
    Concat<Node>(new List<Node>() { Guard }).Concat<Node>(Body);
  public override IEnumerable<INode> PreResolveChildren => Children;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Origin != null);
    Contract.Invariant(Guard != null);
    Contract.Invariant(!IsBindingGuard || (Guard is ExistsExpr && ((ExistsExpr)Guard).Range == null));
    Contract.Invariant(Body != null);
  }
  public GuardedAlternative(IOrigin origin, bool isBindingGuard, Expression guard, List<Statement> body) : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(guard != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(body != null);
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Body = body;
    this.Attributes = null;
  }
  public GuardedAlternative(IOrigin origin, bool isBindingGuard, Expression guard, List<Statement> body, Attributes attrs) : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(guard != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(body != null);
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Body = body;
    this.Attributes = attrs;
  }
}