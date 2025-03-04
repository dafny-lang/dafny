#nullable enable
using System;
using System.Collections;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny;

public class SourceOrigin : IOrigin, IComparable<SourceOrigin> {
  public Uri Uri => StartToken.Uri;

  public Token StartToken { get; }

  public Token EndToken => endToken ?? StartToken;

  public bool InclusiveEnd => endToken != null;
  public bool IncludesRange => true;

  public SourceOrigin(Token startToken, Token? endToken, Token? center)
    : this(startToken, endToken, center?.ToLspLocation()) {
  }

  [SyntaxConstructor]
  public SourceOrigin(Token startToken, Token? endToken, Location? center = null) {
    this.endToken = endToken;
    StartToken = startToken;
    Center = center;
    if (Center == null && Uri != null) {
      Center = new Location {
        Uri = DocumentUri.From(Uri),
        Range = this.ToLspRange2()
      };
    }
  }

  public int CompareTo(IToken? other) {
    if (other is IOrigin otherOrigin) {
      int result = StartToken.CompareTo(otherOrigin.StartToken);
      if (result == 0) {
        result = EndToken.CompareTo(otherOrigin.EndToken);
      }

      return result;
    }

    return 1;
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

  public bool IsInherited(ModuleDefinition m) {
    return false;
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

  public Location? Center {
    get;
  }

  public bool IsCopy => false;

  public bool IsSourceToken => !ReferenceEquals(this, NoToken);

  int IToken.kind {
    get => StartToken.kind;
    set => throw new NotImplementedException();
  }

  int IToken.pos {
    get => StartToken.pos;
    set => throw new NotImplementedException();
  }

  int IToken.col {
    get => Center?.Range.Start.Character ?? -1;
    set => throw new NotImplementedException();
  }

  int IToken.line {
    get => Center?.Range.Start.Line + 1 ?? -1;
    set => throw new NotImplementedException();
  }

  string IToken.val {
    get => throw new InvalidOperationException();
    set => throw new InvalidOperationException();
  }

  bool IToken.IsValid => true;

  int IComparable<SourceOrigin>.CompareTo(SourceOrigin? other) {
    throw new NotImplementedException();
  }
}