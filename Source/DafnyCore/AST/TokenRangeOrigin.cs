#nullable enable
using System;

namespace Microsoft.Dafny;

[method: SyntaxConstructor]
[SyntaxBaseType(typeof(IOrigin))]
public class TokenRangeOrigin(Token startToken, Token endToken) : IOrigin {
  public Token EndToken { get; } = endToken;
  public Token StartToken { get; } = startToken;
  public TokenRange ReportingRange => new(StartToken, EndToken);
  public TokenRange EntireRange => ReportingRange;

  public bool IsCopy => false;

  public bool IsInherited(ModuleDefinition m) {
    return false;
  }

  public bool IncludesRange => true;
  public Uri Uri => StartToken.Uri;

  public bool IsSourceToken => StartToken.IsSourceToken;

  public int kind {
    get => StartToken.kind;
    set => StartToken.kind = value;
  }
  public virtual int line {
    get => StartToken.line;
    set => StartToken.line = value;
  }

  public virtual int col {
    get => StartToken.col;
    set => StartToken.col = value;
  }

  public virtual int pos {
    get => StartToken.pos;
    set => StartToken.pos = value;
  }

  public virtual string val {
    get => StartToken.val;
    set => StartToken.val = value;
  }

  public bool IsValid => true;

  public int CompareTo(IOrigin other) {
    return ReportingRange.CompareTo(other.ReportingRange);
  }

  public int CompareTo(Boogie.IToken? other) {
    return StartToken.CompareTo(other);
  }
}