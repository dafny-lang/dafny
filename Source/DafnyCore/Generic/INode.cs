using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public interface INode {
  bool SingleFileToken { get; }
  public Token StartToken => Origin.StartToken;
  public Token EndToken => Origin.EndToken;
  public Location Center => Origin.Center;
  IEnumerable<IOrigin> OwnedTokens { get; }
  IOrigin Origin { get; }
  IEnumerable<INode> Children { get; }
  IEnumerable<INode> PreResolveChildren { get; }
}