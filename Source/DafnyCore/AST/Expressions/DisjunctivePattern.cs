using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class DisjunctivePattern : ExtendedPattern {
  public readonly List<ExtendedPattern> Alternatives;
  public DisjunctivePattern(IToken tok, List<ExtendedPattern> alternatives, bool isGhost = false) : base(tok, isGhost) {
    Contract.Requires(alternatives != null && alternatives.Count > 0);
    this.Alternatives = alternatives;
  }

  public override IEnumerable<INode> Children => Alternatives;
  public override void Resolve(Resolver resolver, ResolutionContext resolutionContext,
    IDictionary<TypeParameter, Type> subst, Type sourceType, bool isGhost, bool mutable,
    bool inPattern, bool inDisjunctivePattern) {

    if (inPattern) {
      resolver.reporter.Error(MessageSource.Resolver, Tok, "Disjunctive patterns are not allowed inside other patterns");
    }
    
    foreach (var alternative in Alternatives) {
      alternative.Resolve(resolver, resolutionContext, subst, sourceType, isGhost, mutable, true, true);
    }
  }

  public override IEnumerable<(BoundVar var, Expression usage)> ReplaceTypesWithBoundVariables(Resolver resolver,
    ResolutionContext resolutionContext) {
    return Enumerable.Empty<(BoundVar var, Expression usage)>();
  }
}