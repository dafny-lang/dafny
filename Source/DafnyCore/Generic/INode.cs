using System.Collections.Generic;

namespace Microsoft.Dafny;

public interface INode {
  bool SingleFileToken { get; }
  public Token StartToken => Origin.StartToken;
  public Token EndToken => Origin.EndToken;
  public Token Center => Origin.Center;
  IEnumerable<Token> OwnedTokens { get; }
  IOrigin Origin { get; }
  IEnumerable<INode> Children { get; }
  IEnumerable<INode> PreResolveChildren { get; }
}