using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class EmptyNode : Node {
  public override RangeToken RangeToken { get; set; } = new(new Token(), new Token());
  public override IToken Tok => new Token();
  public override IEnumerable<Node> Children => Enumerable.Empty<Node>();
  public override IEnumerable<Node> PreResolveChildren => Enumerable.Empty<Node>();
}