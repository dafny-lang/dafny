using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class DisjunctivePattern : ExtendedPattern {
  public readonly List<ExtendedPattern> Alternatives;
  public DisjunctivePattern(IToken tok, List<ExtendedPattern> alternatives, bool isGhost = false) : base(tok, isGhost) {
    Contract.Requires(alternatives != null && alternatives.Count > 0);
    this.Alternatives = alternatives;
  }

  public override IEnumerable<INode> Children => Alternatives;
}