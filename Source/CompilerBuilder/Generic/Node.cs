namespace Microsoft.Dafny;

public interface INode {
  bool SingleFileToken { get; }
  public IToken StartToken => RangeToken.StartToken;
  public IToken EndToken => RangeToken.EndToken;
  IEnumerable<IToken> OwnedTokens { get; }
  RangeToken RangeToken { get; }
  IToken Tok { get; }
  IEnumerable<INode> Children { get; }
  IEnumerable<INode> PreResolveChildren { get; }
}



