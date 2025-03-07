using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class OriginWrapper : IOrigin {

  public readonly IOrigin WrappedToken;
  protected OriginWrapper(IOrigin wrappedToken) {
    Contract.Requires(wrappedToken != null);
    WrappedToken = wrappedToken;
  }

  public virtual bool IsCopy => WrappedToken.IsCopy;

  public virtual int col {
    get { return WrappedToken.col; }
    set { WrappedToken.col = value; }
  }

  public virtual bool IsInherited(ModuleDefinition m) {
    return WrappedToken.IsInherited(m);
  }

  public virtual bool InclusiveEnd => WrappedToken.InclusiveEnd;
  public virtual bool IncludesRange => WrappedToken.IncludesRange;
  public string ActualFilename => WrappedToken.ActualFilename;

  public virtual string Filepath => WrappedToken.Filepath;

  public Uri Uri => WrappedToken.Uri;

  public virtual Token StartToken => WrappedToken.StartToken;
  public virtual Token EndToken => WrappedToken.EndToken;
  public virtual Token Center => WrappedToken.Center;

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

  public int CompareTo(IOrigin other) {
    return WrappedToken.CompareTo(other);
  }

  public int CompareTo(Boogie.IToken other) {
    return WrappedToken.CompareTo(other);
  }
}