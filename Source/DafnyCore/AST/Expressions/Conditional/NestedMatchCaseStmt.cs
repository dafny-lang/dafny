#nullable enable

using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchCaseStmt : NestedMatchCase, IAttributeBearingDeclaration, ICloneable<NestedMatchCaseStmt> {
  public List<Statement> Body;
  public Attributes? Attributes { get; set; }
  string IAttributeBearingDeclaration.WhatKind => "match statement case";

  [SyntaxConstructor]
  public NestedMatchCaseStmt(IOrigin origin, ExtendedPattern pat, List<Statement> body, Attributes? attributes = null)
    : base(origin, pat) {
    Body = body;
    Attributes = attributes;
  }

  private NestedMatchCaseStmt(Cloner cloner, NestedMatchCaseStmt original) : base(original.Origin, original.Pat) {
    Body = original.Body.Select(stmt => cloner.CloneStmt(stmt, false)).ToList();
    Attributes = cloner.CloneAttributes(original.Attributes);
  }

  public NestedMatchCaseStmt Clone(Cloner cloner) {
    return new NestedMatchCaseStmt(cloner, this);
  }
  public override IEnumerable<INode> Children => new[] { Pat }.Concat<Node>(Body).Concat(Attributes?.Args ?? Enumerable.Empty<Node>());
  public override IEnumerable<INode> PreResolveChildren => Children;

  public void Resolve(
    ModuleResolver resolver,
    ResolutionContext resolutionContext,
    Dictionary<TypeParameter, Type> subst,
    Type sourceType) {
    var beforeResolveErrorCount = resolver.Reporter.ErrorCount;

    Pat.Resolve(resolver, resolutionContext, sourceType, resolutionContext.IsGhost, true, false, false);

    // In Dafny, any bound variables introduced in a pattern are in scope throughout the case body, and cannot be shadowed at the top-level
    // of the case body. Because the machinery above creates, for each bound variable, a local variable with the same name and declares that
    // local variable in the case body, we introduce a new scope boundary around the body.
    resolver.Scope.PushMarker();
    resolver.ResolveAttributes(this, resolutionContext);
    var afterResolveErrorCount = resolver.Reporter.ErrorCount;
    if (beforeResolveErrorCount == afterResolveErrorCount) {
      resolver.DominatingStatementLabels.PushMarker();
      foreach (Statement ss in Body) {
        resolver.ResolveStatementWithLabels(ss, resolutionContext);
      }
      resolver.DominatingStatementLabels.PopMarker();
    }
    resolver.Scope.PopMarker();
  }
}
