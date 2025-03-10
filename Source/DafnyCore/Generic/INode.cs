using System.Collections.Generic;

namespace Microsoft.Dafny;

public interface INode {
  bool SingleFileToken { get; }
  public Token StartToken { get; }
  public Token EndToken { get; }

  public Token Center => Origin.Center;
  IEnumerable<Token> OwnedTokens { get; }
  IOrigin Origin { get; }
  IEnumerable<INode> Children { get; }
  IEnumerable<INode> PreResolveChildren { get; }
}