using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class DisjunctivePattern : ExtendedPattern {
  public readonly List<ExtendedPattern> Alternatives;
  public DisjunctivePattern(IToken tok, List<ExtendedPattern> alternatives, bool isGhost = false) : base(tok, isGhost) {
    Contract.Requires(alternatives != null && alternatives.Count > 0);
    this.Alternatives = alternatives;
  }

  public override IEnumerable<Node> Children => Alternatives;
  public override IEnumerable<Node> PreResolveChildren => Children;

  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var alternative in Alternatives) {
        foreach (var ee in alternative.SubExpressions) {
          yield return ee;
        }
      }
    }
  }

  public override void Resolve(Resolver resolver, ResolutionContext resolutionContext,
    Type sourceType, bool isGhost, bool inStatementContext,
    bool inPattern, bool inDisjunctivePattern) {

    if (inPattern) {
      resolver.reporter.Error(MessageSource.Resolver, Tok, "Disjunctive patterns are not allowed inside other patterns");
    }

    foreach (var alternative in Alternatives) {
      alternative.Resolve(resolver, resolutionContext, sourceType, isGhost, inStatementContext, true, true);
    }
  }

  public override IEnumerable<(BoundVar var, Expression usage)> ReplaceTypesWithBoundVariables(Resolver resolver,
    ResolutionContext resolutionContext) {
    return Enumerable.Empty<(BoundVar var, Expression usage)>();
  }
}