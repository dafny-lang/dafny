using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchExpr : Expression, ICloneable<NestedMatchExpr> {
  public readonly Expression Source;
  public readonly List<NestedMatchCaseExpr> Cases;
  public readonly bool UsesOptionalBraces;
  public Attributes Attributes;

  [FilledInDuringResolution]
  public Expression Denested { get; set; }

  public NestedMatchExpr(Cloner cloner, NestedMatchExpr original) : base(cloner, original) {
    this.Source = cloner.CloneExpr(original.Source);
    this.Cases = original.Cases.Select(cloner.CloneNestedMatchCaseExpr).ToList();
    this.UsesOptionalBraces = original.UsesOptionalBraces;
    if (cloner.CloneResolvedFields) {
      Denested = cloner.CloneExpr(original.Denested);
    }
  }

  public NestedMatchExpr(IToken tok, Expression source, [Captured] List<NestedMatchCaseExpr> cases, bool usesOptionalBraces, Attributes attrs = null) : base(tok) {
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    this.Source = source;
    this.Cases = cases;
    this.UsesOptionalBraces = usesOptionalBraces;
    this.Attributes = attrs;
  }

  public override IEnumerable<Expression> SubExpressions =>
    new[] { Source }.Concat(Cases.Select(c => c.Body));

  public override IEnumerable<INode> Children => new[] { Source }.Concat<INode>(Cases);

  public void Resolve(Resolver resolver, ResolutionContext resolutionContext) {

    resolver.ResolveExpression(Source, resolutionContext);

    if (Source.Type is TypeProxy) {
      resolver.PartiallySolveTypeConstraints(true);

      if (Source.Type is TypeProxy) {
        resolver.reporter.Error(MessageSource.Resolver, tok, "Could not resolve the type of the source of the match expression. Please provide additional typing annotations.");
        return;
      }
    }

    var errorCount = resolver.reporter.Count(ErrorLevel.Error);
    var sourceType = resolver.PartiallyResolveTypeForMemberSelection(Source.tok, Source.Type).NormalizeExpand();
    if (resolver.reporter.Count(ErrorLevel.Error) != errorCount) {
      return;
    }

    resolver.CheckLinearNestedMatchExpr(sourceType, this, resolutionContext);
    if (resolver.reporter.Count(ErrorLevel.Error) != errorCount) {
      return;
    }

    var dtd = sourceType.AsDatatype;
    var subst = new Dictionary<TypeParameter, Type>();
    if (dtd != null) {
      subst = TypeParameter.SubstitutionMap(dtd.TypeArgs, sourceType.TypeArgs);
    }

    Type = new InferredTypeProxy();
    foreach (var kase in Cases) {
      resolver.scope.PushMarker();
      kase.Resolve(resolver, resolutionContext, subst, Type, sourceType);
      resolver.scope.PopMarker();
    }
  }

  public NestedMatchExpr Clone(Cloner cloner) {
    return new NestedMatchExpr(cloner, this);
  }
}
