using System.Collections.Generic;

namespace Microsoft.Dafny;

public interface INode {
  bool SingleFileToken { get; }
  
  public Token Center => Origin.Center; // TODO inline
  public Token StartToken => Origin.StartToken; // TODO inline
  public Token EndToken => Origin.EndToken; // TODO inline
  IEnumerable<IOrigin> OwnedTokens { get; }
  IOrigin Origin { get; }
  IOrigin RangeToken { get; } // TODO remove
  IOrigin Tok { get; } // TODO remove
  IEnumerable<INode> Children { get; }
  IEnumerable<INode> PreResolveChildren { get; }
}