using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class HavocRhs : AssignmentRhs, ICloneable<HavocRhs> {
  public HavocRhs Clone(Cloner cloner) {
    return new HavocRhs(cloner, this);
  }
  public HavocRhs(IToken tok) : base(tok) {
  }

  private HavocRhs(Cloner cloner, HavocRhs havocRhs) : base(cloner, havocRhs) {
  }

  public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  public override IEnumerable<Node> Children => Enumerable.Empty<Node>();
  public override IEnumerable<Node> PreResolveChildren => Enumerable.Empty<Node>();
}