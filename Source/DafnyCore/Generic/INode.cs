using System.Collections.Generic;

namespace Microsoft.Dafny;

public interface INode {
  bool SingleFileToken { get; }
  public Token Center { get; }
  public Token StartToken => RangeToken.StartToken;
  public Token EndToken => RangeToken.EndToken;
  IEnumerable<IOrigin> OwnedTokens { get; }
  IOrigin RangeToken { get; }
  IOrigin Tok { get; }
  IEnumerable<INode> Children { get; }
  IEnumerable<INode> PreResolveChildren { get; }
}