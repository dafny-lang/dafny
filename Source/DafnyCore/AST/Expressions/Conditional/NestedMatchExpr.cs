using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

interface INestedMatch : INode {
  Expression Source { get; }
  string MatchTypeName { get; }
  IReadOnlyList<NestedMatchCase> Cases { get; }
}

public class NestedMatchExpr : Expression, ICloneable<NestedMatchExpr>, ICanFormat, INestedMatch {
  public Expression Source { get; }
  public string MatchTypeName => "expression";
  public List<NestedMatchCaseExpr> Cases { get; }

  IReadOnlyList<NestedMatchCase> INestedMatch.Cases => Cases;

  public bool UsesOptionalBraces;
  public Attributes Attributes;

  [FilledInDuringResolution]
  public Expression Flattened { get; set; }

  public NestedMatchExpr(Cloner cloner, NestedMatchExpr original) : base(cloner, original) {
    this.Source = cloner.CloneExpr(original.Source);
    this.Cases = original.Cases.Select(cloner.CloneNestedMatchCaseExpr).ToList();
    this.UsesOptionalBraces = original.UsesOptionalBraces;

    if (cloner.CloneResolvedFields) {
      Flattened = cloner.CloneExpr(original.Flattened);
    }
  }

  public NestedMatchExpr(IOrigin origin, Expression source, [Captured] List<NestedMatchCaseExpr> cases, bool usesOptionalBraces, Attributes attrs = null) : base(origin) {
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    this.Source = source;
    this.Cases = cases;
    this.UsesOptionalBraces = usesOptionalBraces;
    this.Attributes = attrs;
  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      yield return Source;
      foreach (var mc in Cases) {
        foreach (var ee in mc.Pat.SubExpressions) {
          yield return ee;
        }
        yield return mc.Body;
      }
    }
  }

  public override IEnumerable<INode> Children => new[] { Source }.Concat<Node>(Cases);

  public void Resolve(ModuleResolver resolver, ResolutionContext resolutionContext) {

    resolver.ResolveExpression(Source, resolutionContext);

    if (Source.Type is TypeProxy) {
      resolver.PartiallySolveTypeConstraints(true);

      if (Source.Type is TypeProxy) {
        resolver.reporter.Error(MessageSource.Resolver, Origin, "Could not resolve the type of the source of the match expression. Please provide additional typing annotations.");
        return;
      }
    }

    var errorCount = resolver.reporter.Count(ErrorLevel.Error);
    var sourceType = resolver.PartiallyResolveTypeForMemberSelection(Source.Origin, Source.Type).NormalizeExpand();
    if (resolver.reporter.Count(ErrorLevel.Error) != errorCount) {
      return;
    }

    foreach (NestedMatchCaseExpr mc in Cases) {
      resolver.scope.PushMarker();
      resolver.ResolveAttributes(mc, resolutionContext);
      mc.CheckLinearNestedMatchCase(sourceType, resolutionContext, resolver);
      resolver.scope.PopMarker();
    }

    if (resolver.reporter.Count(ErrorLevel.Error) != errorCount) {
      return;
    }

    Type = new InferredTypeProxy();
    foreach (var kase in Cases) {
      resolver.scope.PushMarker();
      kase.Resolve(resolver, resolutionContext, Type, sourceType);
      resolver.scope.PopMarker();
    }
  }

  public NestedMatchExpr Clone(Cloner cloner) {
    return new NestedMatchExpr(cloner, this);
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentCases(indentBefore, OwnedTokens.Concat(Cases.SelectMany(oneCase => oneCase.OwnedTokens)).OrderBy(token => token.pos), () => {
      foreach (var e in formatter.SubExpressions(this)) {
        formatter.Visit(e, indentBefore);
      }
    });
  }
}
