#nullable enable
using System;
using System.Text;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class SourceOrigin : IOrigin {
  public Uri Uri {
    get => Center.Uri;
    set => throw new InvalidOperationException();
  }

  public Token StartToken { get; }

  public Token EndToken => endToken ?? StartToken;

  public bool IsInherited(ModuleDefinition m) {
    return false;
  }

  public bool InclusiveEnd => endToken != null;
  public bool IncludesRange => true;

  public int CompareTo(IToken? other) {
    if (other == null) {
      return 1;
    }
    return Center.CompareTo(other);
  }

  public int CompareTo(IOrigin? other) {
    if (other == null) {
      return 1;
    }
    return Center.CompareTo(other.Center);
  }

  public override bool Equals(object? obj) {
    if (obj is SourceOrigin other) {
      return StartToken.Equals(other.StartToken) && EndToken.Equals(other.EndToken);
    }
    return false;
  }

  public override int GetHashCode() {
    return HashCode.Combine(StartToken.GetHashCode(), EndToken.GetHashCode());
  }

  public SourceOrigin(Token startToken, Token? endToken, Token? center = null) {
    this.endToken = endToken;
    StartToken = startToken;
    Center = center ?? startToken;
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

  public int Length() {
    return EndToken.pos - StartToken.pos;
  }

  // TODO rename to Generated, and Token.NoToken to Token.Generated, and remove AutoGeneratedToken.
  public static IOrigin NoToken => Token.NoToken;
  private readonly Token? endToken;

  public Token Center {
    get;
  }
  public string TrailingTrivia {
    get => Center.TrailingTrivia;
    set => throw new InvalidOperationException();
  }

  public string LeadingTrivia {
    get => Center.LeadingTrivia;
    set => throw new InvalidOperationException();
  }

  public Token Next {
    get => Center.Next;
    set => throw new InvalidOperationException();
  }

  public Token Prev {
    get => Center.Prev;
    set => throw new InvalidOperationException();
  }

  public IOrigin WithVal(string newVal) {
    throw new NotImplementedException();
  }

  public bool IsCopy => false;

  public bool IsSourceToken => !ReferenceEquals(this, NoToken);
  public int kind {
    get => Center.kind;
    set => throw new NotImplementedException();
  }

  public int pos {
    get => Center.pos;
    set => throw new NotImplementedException();
  }

  public int col {
    get => Center.col;
    set => throw new NotImplementedException();
  }

  public int line {
    get => Center.line;
    set => throw new NotImplementedException();
  }

  public string val {
    get => Center.val;
    set => throw new InvalidOperationException();
  }

  public bool IsValid => true;
}