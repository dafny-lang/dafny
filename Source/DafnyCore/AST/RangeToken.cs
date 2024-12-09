#nullable enable
using System;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class RangeToken : IOrigin {
  public bool IsMissingRange => false;

  public bool IsInherited(ModuleDefinition d) {
    return false;
  }

  public override bool Equals(object? obj) {
    if (obj is RangeToken other) {
      return StartToken.Equals(other.StartToken) && EndToken.Equals(other.EndToken);
    }

    return false;
  }

  public override int GetHashCode() {
    return HashCode.Combine(StartToken.GetHashCode(), EndToken.GetHashCode());
  }

  public Token Center { get; }

  public Token StartToken { get; }
  public Token Centre => Center;

  public Token EndToken => endToken ?? StartToken;
  public bool ContainsRange => true;

  public bool InclusiveEnd => endToken != null;

  public RangeToken(Token startToken, Token? endToken, Token? center = null) {
    StartToken = startToken;
    Center = center ?? startToken;
    this.endToken = endToken;
  }
  public int Length() {
    return EndToken.pos - StartToken.pos;
  }

  public static IOrigin NoToken => Token.NoToken; // TODO inline
  private readonly Token? endToken;

  public Uri Uri {
    get => Center.Uri;
    set => Center.Uri = value;
  }

  public string TrailingTrivia {
    get => Center.TrailingTrivia;
    set => Center.TrailingTrivia = value;
  }

  public string LeadingTrivia {
    get => Center.LeadingTrivia;
    set => Center.LeadingTrivia = value;
  }

  public Token Next {
    get => Center.Next;
    set => Center.Next = value;
  }

  public Token Prev {
    get => Center.Prev;
    set => Center.Prev = value;
  }

  public IOrigin WithVal(string newValue) {
    throw new NotImplementedException(); // TODO why is this needed?
  }

  public bool IsCopy => false;

  public bool IsSourceToken => true;

  public int kind {
    get => Center.kind;
    set => Center.kind = value;
  }

  public int pos {
    get => Center.pos;
    set => Center.pos = value;
  }

  public int col {
    get => Center.col;
    set => Center.col = value;
  }

  public int line {
    get => Center.line;
    set => Center.line = value;
  }

  public string val {
    get => Center.val;
    set => Center.val = value;
  }

  public bool IsValid => Center.IsValid;

  public BoogieRangeOrigin ToToken() {
    return new BoogieRangeOrigin(StartToken, EndToken, null);
  }

  public int CompareTo(IToken? other) {
    return Center.CompareTo(other);
  }

  public int CompareTo(IOrigin? other) {
    return Center.CompareTo((IToken)other!);
  }
}