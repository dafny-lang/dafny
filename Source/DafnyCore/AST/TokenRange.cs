#nullable enable
using System;
using System.Text;

namespace Microsoft.Dafny;

public class TokenRange(Token startToken, Token? endToken) : IComparable<TokenRange>, IEquatable<TokenRange> {

  public Token? Prev => StartToken.Prev;
  public Token Next => EndToken.Next;

  public bool InclusiveEnd => endToken != null;

  public Token StartToken { get; } = startToken;

  public Token EndToken => endToken ?? StartToken;

  public Uri Uri => StartToken.Uri;
  public int Length => EndToken.pos - StartToken.pos + EndLength;

  public int EndLength => InclusiveEnd ? EndToken.val.Length : 0;

  public int CompareTo(TokenRange? other) {
    if (other == null) {
      return 1;
    }
    var startResult = StartToken.CompareTo(other.StartToken);
    if (startResult != 0) {
      return startResult;
    }

    return EndToken.CompareTo(other.EndToken);
  }

  public string PrintOriginal() {
    var token = StartToken;
    var originalString = new StringBuilder();
    originalString.Append(token.val);
    while (token.Next != null && token.pos < EndToken.pos) {
      originalString.Append(token.TrailingTrivia);
      token = token.Next;
      originalString.Append(token.LeadingTrivia);
      originalString.Append(token.val);
    }

    return originalString.ToString();
  }

  public DafnyRange ToDafnyRange(bool includeTrailingWhitespace = false) {
    var startLine = StartToken.line - 1;
    var startColumn = StartToken.col - 1;
    int whitespaceOffset = 0;
    if (includeTrailingWhitespace) {
      string trivia = (EndToken).TrailingTrivia;
      // Don't want to remove newlines or comments -- just spaces and tabs
      while (whitespaceOffset < trivia.Length && (trivia[whitespaceOffset] == ' ' || trivia[whitespaceOffset] == '\t')) {
        whitespaceOffset++;
      }
    }

    var endColumn = (endToken == null ? StartToken.col : endToken.col + endToken.val.Length) + whitespaceOffset - 1;
    var endLine = EndToken.line - 1;
    return new DafnyRange(
      new DafnyPosition(startLine, startColumn),
      new DafnyPosition(endLine, endColumn));
  }

  public bool Equals(TokenRange? other) {
    if (ReferenceEquals(null, other)) {
      return false;
    }

    if (ReferenceEquals(this, other)) {
      return true;
    }

    return StartToken.Equals(other.StartToken) && EndToken.Equals(other.EndToken);
  }

  public override bool Equals(object? obj) {
    if (ReferenceEquals(null, obj)) {
      return false;
    }

    if (ReferenceEquals(this, obj)) {
      return true;
    }

    if (obj.GetType() != this.GetType()) {
      return false;
    }

    return Equals((TokenRange)obj);
  }

  public override int GetHashCode() {
    return HashCode.Combine(StartToken.GetHashCode(), EndToken?.GetHashCode() ?? 0);
  }
}