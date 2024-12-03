using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class OriginWrapper : IOrigin {

  public readonly IOrigin WrappedToken;
  protected OriginWrapper(IOrigin wrappedToken) {
    Contract.Requires(wrappedToken != null);
    WrappedToken = wrappedToken;
  }

  public abstract IOrigin WithVal(string newVal);

  public virtual int col {
    get { return WrappedToken.col; }
    set { WrappedToken.col = value; }
  }

  public string ActualFilename => WrappedToken.ActualFilename;

  public virtual string Filepath => WrappedToken.Filepath;

  public Uri Uri {
    get => WrappedToken.Uri;
    set => WrappedToken.Uri = value;
  }

  public bool IsValid {
    get { return WrappedToken.IsValid; }
  }

  public virtual bool IsSourceToken => false;

  public int kind {
    get { return WrappedToken.kind; }
    set { WrappedToken.kind = value; }
  }
  public virtual int line {
    get { return WrappedToken.line; }
    set { WrappedToken.line = value; }
  }
  public virtual int pos {
    get { return WrappedToken.pos; }
    set { WrappedToken.pos = value; }
  }

  public virtual string val {
    get { return WrappedToken.val; }
    set { WrappedToken.val = value; }
  }
  public virtual string LeadingTrivia {
    get { return WrappedToken.LeadingTrivia; }
    set { throw new NotSupportedException(); }
  }
  public virtual string TrailingTrivia {
    get { return WrappedToken.TrailingTrivia; }
    set { throw new NotSupportedException(); }
  }
  public virtual IOrigin Next {
    get { return WrappedToken.Next; }
    set { throw new NotSupportedException(); }
  }
  public virtual IOrigin Prev {
    get { return WrappedToken.Prev; }
    set { throw new NotSupportedException(); }
  }

  public int CompareTo(IOrigin other) {
    return WrappedToken.CompareTo(other);
  }

  public int CompareTo(Boogie.IToken other) {
    return WrappedToken.CompareTo(other);
  }

  /// <summary>
  ///  Removes token wrappings from a given token, so that it returns the bare token
  /// </summary>
  public static IOrigin Unwrap(IOrigin token, bool includeRanges = false) {
    if (token is OriginWrapper wrapper
        && (includeRanges || token is not RangeToken)) {
      return Unwrap(wrapper.WrappedToken);
    }

    if (token is RangeToken rangeToken) {
      return new RangeToken(Unwrap(rangeToken.StartToken), Unwrap(rangeToken.EndToken));
    }

    return token;
  }
}