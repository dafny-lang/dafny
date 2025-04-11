#nullable enable

using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchCaseExpr : NestedMatchCase, IAttributeBearingDeclaration {
  public Expression Body;
  public Attributes? Attributes { get; set; }

  string IAttributeBearingDeclaration.WhatKind => "match expression case";

  [SyntaxConstructor]
  public NestedMatchCaseExpr(IOrigin origin, ExtendedPattern pat, Expression body, Attributes? attributes = null)
    : base(origin, pat) {
    Body = body;
    Attributes = attributes;
  }

  public override IEnumerable<INode> Children =>
    Attributes.AsEnumerable().
      Concat(new Node[] { Body, Pat });

  public override IEnumerable<INode> PreResolveChildren => Children;

  public void Resolve(ModuleResolver resolver,
    ResolutionContext resolutionContext,
    Type resultType,
    Type sourceType) {
    var beforeResolveErrorCount = resolver.reporter.ErrorCount;

    Pat.Resolve(resolver, resolutionContext, sourceType, resolutionContext.IsGhost, false, false, false);

    resolver.ResolveAttributes(this, resolutionContext);
    var afterResolveErrorCount = resolver.reporter.ErrorCount;
    if (beforeResolveErrorCount == afterResolveErrorCount) {
      resolver.ResolveExpression(Body, resolutionContext);
      resolver.ConstrainSubtypeRelation(resultType, Body.Type, Body.Origin, "type of case bodies do not agree (found {0}, previous types {1})", Body.Type, resultType);
    }
  }

  public override string ToString() {
    var writer = new StringWriter();
    new Printer(writer, DafnyOptions.Default).PrintNestedMatchCase(false, false, this, false, false);
    return writer.ToString();
  }
}
