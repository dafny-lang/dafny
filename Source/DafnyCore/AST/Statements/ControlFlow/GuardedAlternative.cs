using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class GuardedAlternative : TokenNode, IAttributeBearingDeclaration {
  public readonly bool IsBindingGuard;
  public readonly Expression Guard;
  public readonly List<Statement> Body;
  public Attributes Attributes { get; set; }
  string IAttributeBearingDeclaration.WhatKind => "alternative-based case";
  public override IEnumerable<INode> Children => Attributes.AsEnumerable().
    Concat<Node>(new List<Node>() { Guard }).Concat<Node>(Body);
  public override IEnumerable<INode> PreResolveChildren => Children;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Tok != null);
    Contract.Invariant(Guard != null);
    Contract.Invariant(!IsBindingGuard || (Guard is ExistsExpr && ((ExistsExpr)Guard).Range == null));
    Contract.Invariant(Body != null);
  }
  public GuardedAlternative(IOrigin tok, bool isBindingGuard, Expression guard, List<Statement> body) {
    Contract.Requires(tok != null);
    Contract.Requires(guard != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(body != null);
    this.tok = tok;
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Body = body;
    this.Attributes = null;
  }
  public GuardedAlternative(IOrigin tok, bool isBindingGuard, Expression guard, List<Statement> body, Attributes attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(guard != null);
    Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
    Contract.Requires(body != null);
    this.tok = tok;
    this.IsBindingGuard = isBindingGuard;
    this.Guard = guard;
    this.Body = body;
    this.Attributes = attrs;
  }
}