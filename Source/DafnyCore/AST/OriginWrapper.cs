using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class OriginWrapper : IOrigin {

  public readonly IOrigin WrappedOrigin;
  protected OriginWrapper(IOrigin wrappedOrigin) {
    Contract.Requires(wrappedOrigin != null);
    WrappedOrigin = wrappedOrigin;
  }

  public virtual TokenRange ReportingRange => WrappedOrigin.ReportingRange;
  public virtual bool IsCopy => WrappedOrigin.IsCopy;

  public virtual int col {
    get { return WrappedOrigin.col; }
    set { WrappedOrigin.col = value; }
  }

  public virtual bool IsInherited(ModuleDefinition m) {
    return WrappedOrigin.IsInherited(m);
  }
  public virtual bool IncludesRange => WrappedOrigin.IncludesRange;
  public string ActualFilename => WrappedOrigin.ActualFilename;

  public virtual string Filepath => WrappedOrigin.Filepath;

  public Uri Uri => WrappedOrigin.Uri;

  public virtual TokenRange EntireRange => WrappedOrigin.EntireRange;

  public bool IsValid {
    get { return WrappedOrigin.IsValid; }
  }

  public virtual bool IsSourceToken => false;

  public int kind {
    get { return WrappedOrigin.kind; }
    set { WrappedOrigin.kind = value; }
  }
  public virtual int line {
    get { return WrappedOrigin.line; }
    set { WrappedOrigin.line = value; }
  }
  public virtual int pos {
    get { return WrappedOrigin.pos; }
    set { WrappedOrigin.pos = value; }
  }

  public virtual string val {
    get { return WrappedOrigin.val; }
    set { WrappedOrigin.val = value; }
  }

  public int CompareTo(IOrigin other) {
    return WrappedOrigin.CompareTo(other);
  }

  public int CompareTo(Boogie.IToken other) {
    return WrappedOrigin.CompareTo(other);
  }
}