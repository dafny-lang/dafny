using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class HavocRhs : AssignmentRhs {
  public HavocRhs(IToken tok)
    : base(tok) {
  }
  public override bool CanAffectPreviouslyKnownExpressions { get { return false; } }
  public override IEnumerable<Node> Children => Enumerable.Empty<Node>();
  public override IEnumerable<Node> PreResolveChildren => Enumerable.Empty<Node>();
}