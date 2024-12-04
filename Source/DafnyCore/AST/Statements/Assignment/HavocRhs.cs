using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class HavocRhs : AssignmentRhs, ICloneable<HavocRhs> {
  public HavocRhs Clone(Cloner cloner) {
    return new HavocRhs(cloner, this);
  }
  public HavocRhs(IOrigin tok) : base(tok) {
  }

  private HavocRhs(Cloner cloner, HavocRhs havocRhs) : base(cloner, havocRhs) {
  }

  public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();
  public override IEnumerable<INode> PreResolveChildren => Enumerable.Empty<Node>();

  public void Resolve(INewOrOldResolver resolver, ResolutionContext resolutionContext) {
    if (!resolutionContext.IsGhost && resolver.Options.ForbidNondeterminism) {
      resolver.Reporter.Error(MessageSource.Resolver, GeneratorErrors.ErrorId.c_nondeterminism_forbidden, Tok, "nondeterministic assignment forbidden by the --enforce-determinism option");
    }
  }
}