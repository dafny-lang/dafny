using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchCaseExpr : NestedMatchCase, IAttributeBearingDeclaration {
  public Expression Body;
  public Attributes Attributes { get; set; }

  string IAttributeBearingDeclaration.WhatKind => "match expression case";

  public NestedMatchCaseExpr(IOrigin tok, ExtendedPattern pat, Expression body, Attributes attrs) : base(tok, pat) {
    Contract.Requires(body != null);
    this.Body = body;
    this.Attributes = attrs;
  }

  public override IEnumerable<INode> Children =>
    Attributes.AsEnumerable().
      Concat<Node>(new Node[] { Body, Pat });

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
      resolver.ConstrainSubtypeRelation(resultType, Body.Type, Body.Tok, "type of case bodies do not agree (found {0}, previous types {1})", Body.Type, resultType);
    }
  }

  public override string ToString() {
    var writer = new StringWriter();
    new Printer(writer, DafnyOptions.Default).PrintNestedMatchCase(false, false, this, false, false);
    return writer.ToString();
  }
}
