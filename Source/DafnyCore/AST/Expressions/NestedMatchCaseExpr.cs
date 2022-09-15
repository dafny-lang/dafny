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

  public override IEnumerable<INode> Children => new INode[] { Body, Pat }.Concat(Attributes?.Args ?? Enumerable.Empty<INode>());

  public void Resolve(
    Resolver resolver,
    ResolutionContext resolutionContext,
    Dictionary<TypeParameter, Type> subst,
    Type caseType,
    Type sourceType) {
    var errorCount = resolver.reporter.ErrorCount;

    var bindings = Pat.ReplaceTypesWithBoundVariables(resolver, resolutionContext).ToList();
    if (bindings.Any()) {
      var lhss = bindings.Select(b => new CasePattern<BoundVar>(Token.NoToken, b)).ToList();
      var rhss = bindings.Select<BoundVar, Expression>(b => new IdentifierExpr(Token.NoToken, b));
    
      Body = new LetExpr(Token.NoToken, lhss, rhss.ToList(), Body, true);
    }
    
    Pat.Resolve(resolver, resolutionContext, subst, sourceType, false); // TODO: is this false correct?
    resolver.ResolveAttributes(this, resolutionContext);
    var errorCount2 = resolver.reporter.ErrorCount;
    if (errorCount == errorCount2) {
      resolver.ResolveExpression(Body, resolutionContext);
      resolver.ConstrainSubtypeRelation(caseType, Body.Type, Body.tok, "type of case bodies do not agree (found {0}, previous types {1})", Body.Type, caseType);
    }
  }
}