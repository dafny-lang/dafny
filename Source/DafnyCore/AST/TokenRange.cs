#nullable enable
using System;
using System.Text;

namespace Microsoft.Dafny;

public class TokenRange(Token start, Token? end) : IComparable<TokenRange> {
  public Token Start { get; } = start;

  public Token End => end ?? Start;

  public Uri Uri => Start.Uri;

  public int CompareTo(TokenRange? other) {
    if (other == null) {
      return 1;
    }
    var startResult = Start.CompareTo(other.Start);
    if (startResult != 0) {
      return startResult;
    }

    return End.CompareTo(other.End);
  }
  
  public string PrintOriginal() {
    var token = Start;
    var originalString = new StringBuilder();
    originalString.Append(token.val);
    while (token.Next != null && token.pos < End.pos) {
      originalString.Append(token.TrailingTrivia);
      token = token.Next;
      originalString.Append(token.LeadingTrivia);
      originalString.Append(token.val);
    }

    return originalString.ToString();
  }
}