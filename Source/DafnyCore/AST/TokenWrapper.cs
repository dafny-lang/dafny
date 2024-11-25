using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class TokenWrapper : IOrigin {

  public readonly IOrigin WrappedOrigin;
  protected TokenWrapper(IOrigin wrappedOrigin) {
    Contract.Requires(wrappedOrigin != null);
    WrappedOrigin = wrappedOrigin;
  }

  public abstract IOrigin WithVal(string newVal);

  public virtual int col {
    get => WrappedOrigin.col;
    set => WrappedOrigin.col = value;
  }

  public Token StartToken => WrappedOrigin.StartToken;
  public Token EndToken => WrappedOrigin.EndToken;
  public bool ContainsRange => WrappedOrigin.ContainsRange;
  public string ActualFilename => WrappedOrigin.ActualFilename;

  public virtual string Filepath => WrappedOrigin.Filepath;

  public Uri Uri {
    get => WrappedOrigin.Uri;
    set => WrappedOrigin.Uri = value;
  }

  public bool IsValid => WrappedOrigin.IsValid;

  public virtual bool IsSourceToken => false;

  public int kind {
    get => WrappedOrigin.kind;
    set => WrappedOrigin.kind = value;
  }
  public virtual int line {
    get => WrappedOrigin.line;
    set => WrappedOrigin.line = value;
  }
  public virtual int pos {
    get => WrappedOrigin.pos;
    set => WrappedOrigin.pos = value;
  }

  public virtual string val {
    get => WrappedOrigin.val;
    set => WrappedOrigin.val = value;
  }
  public virtual string LeadingTrivia {
    get => WrappedOrigin.LeadingTrivia;
    set => throw new NotSupportedException();
  }
  public virtual string TrailingTrivia {
    get => WrappedOrigin.TrailingTrivia;
    set => throw new NotSupportedException();
  }
  public virtual Token Next {
    get => WrappedOrigin.Next;
    set => throw new NotSupportedException();
  }
  public virtual Token Prev {
    get => WrappedOrigin.Prev;
    set => throw new NotSupportedException();
  }

  public int CompareTo(IOrigin other) {
    return WrappedOrigin.CompareTo(other);
  }

  public int CompareTo(Boogie.IToken other) {
    return WrappedOrigin.CompareTo(other);
  }
}