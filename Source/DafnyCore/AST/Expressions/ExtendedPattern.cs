using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

/*
ExtendedPattern is either:
1 - A LitPattern of a LiteralExpr, representing a constant pattern
2 - An IdPattern of a string and a list of ExtendedPattern, representing either
    a bound variable or a constructor applied to n arguments or a symbolic constant
*/
public abstract class ExtendedPattern : INode {
  public bool IsGhost;

  public ExtendedPattern(IToken tok, bool isGhost = false) {
    Contract.Requires(tok != null);
    this.Tok = tok;
    this.IsGhost = isGhost;
  }

  public IEnumerable<INode> DescendantsAndSelf =>
    new[] { this }.Concat(Children.OfType<ExtendedPattern>().SelectMany(c => c.DescendantsAndSelf));

  public abstract void Resolve(Resolver resolver, ResolutionContext resolutionContext,
    IDictionary<TypeParameter, Type> subst, Type sourceType, bool isGhost, bool mutable,
    bool inPattern, bool inDisjunctivePattern);

  public abstract IEnumerable<(BoundVar var, Expression usage)> ReplaceTypesWithBoundVariables(Resolver resolver,
    ResolutionContext resolutionContext);
}