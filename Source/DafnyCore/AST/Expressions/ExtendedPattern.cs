using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class ExtendedPattern : INode {
  public bool IsGhost;

  public ExtendedPattern(IToken tok, bool isGhost = false) {
    Contract.Requires(tok != null);
    this.Tok = tok;
    this.IsGhost = isGhost;
  }

  public IEnumerable<INode> DescendantsAndSelf =>
    new[] { this }.Concat(Children.OfType<ExtendedPattern>().SelectMany(c => c.DescendantsAndSelf));
}