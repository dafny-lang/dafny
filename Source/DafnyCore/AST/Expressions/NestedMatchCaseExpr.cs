using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchCaseExpr : NestedMatchCase, IAttributeBearingDeclaration {
  public Expression Body;
  public Attributes Attributes;
  Attributes IAttributeBearingDeclaration.Attributes => Attributes;

  public NestedMatchCaseExpr(IToken tok, ExtendedPattern pat, Expression body, Attributes attrs) : base(tok, pat) {
    Contract.Requires(body != null);
    this.Body = body;
    this.Attributes = attrs;
  }

  public override IEnumerable<INode> Children =>
    (Attributes != null ? new INode[] { Attributes } : Enumerable.Empty<INode>()).Concat(new INode[] { Body, Pat });

  public void Resolve(Resolver resolver,
    ResolutionContext resolutionContext,
    Type resultType,
    Type sourceType) {
    var beforeResolveErrorCount = resolver.reporter.ErrorCount;

    var boundVars = Pat.ReplaceTypesWithBoundVariables(resolver, resolutionContext).ToList();
    if (boundVars.Any()) {
      var lhss = boundVars.Select(b => new CasePattern<BoundVar>(Token.NoToken, b.var)).ToList();
      var rhss = boundVars.Select(b => b.usage).ToList();

      Body = new LetExpr(Token.NoToken, lhss, rhss, Body, true);
    }

    Pat.Resolve(resolver, resolutionContext, sourceType, false, false, false, false);

    resolver.ResolveAttributes(this, resolutionContext);
    var afterResolveErrorCount = resolver.reporter.ErrorCount;
    if (beforeResolveErrorCount == afterResolveErrorCount) {
      resolver.ResolveExpression(Body, resolutionContext);
      resolver.ConstrainSubtypeRelation(resultType, Body.Type, Body.tok, "type of case bodies do not agree (found {0}, previous types {1})", Body.Type, resultType);
    }
  }
}
