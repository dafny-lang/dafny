using System.Collections.Generic;

namespace Microsoft.Dafny;

public interface INode {
  bool SingleFileToken { get; }
  public TokenRange EntireRange { get; }


  
  public Token StartToken => EntireRange.Start;
  public Token EndToken => EntireRange.End;

  public TokenRange ReportingRange => Origin.ReportingRange;

  IEnumerable<Token> OwnedTokens { get; }
  IOrigin Origin { get; }
  IEnumerable<INode> Children { get; }
  IEnumerable<INode> PreResolveChildren { get; }
}