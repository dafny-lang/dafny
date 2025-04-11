#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class DisjunctivePattern : ExtendedPattern {
  public List<ExtendedPattern> Alternatives;

  [SyntaxConstructor]
  public DisjunctivePattern(IOrigin origin, List<ExtendedPattern> alternatives, bool isGhost = false) : base(origin, isGhost) {
    Contract.Requires(alternatives.Count > 0);
    Alternatives = alternatives;
  }

  public override IEnumerable<INode> Children => Alternatives;
  public override IEnumerable<INode> PreResolveChildren => Children;

  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var alternative in Alternatives) {
        foreach (var ee in alternative.SubExpressions) {
          yield return ee;
        }
      }
    }
  }

  public override void Resolve(ModuleResolver resolver, ResolutionContext resolutionContext,
    Type sourceType, bool isGhost, bool inStatementContext,
    bool inPattern, bool inDisjunctivePattern) {

    if (inPattern) {
      resolver.reporter.Error(MessageSource.Resolver, Origin, "Disjunctive patterns are not allowed inside other patterns");
    }

    foreach (var alternative in Alternatives) {
      alternative.Resolve(resolver, resolutionContext, sourceType, isGhost, inStatementContext, true, true);
    }
  }
}