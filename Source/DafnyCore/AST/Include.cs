using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class Include : TokenNode, IComparable {
  public Uri IncluderFilename { get; }
  public Uri IncludedFilename { get; }
  public string CanonicalPath { get; }

  public Include(IToken tok, Uri includer, Uri theFilename) {
    this.tok = tok;
    this.IncluderFilename = includer;
    this.IncludedFilename = theFilename;
    this.CanonicalPath = DafnyFile.Canonicalize(theFilename.LocalPath).LocalPath;
  }

  public int CompareTo(object obj) {
    if (obj is Include include) {
      return CanonicalPath.CompareTo(include.CanonicalPath);
    } else {
      throw new NotImplementedException();
    }
  }

  public override IEnumerable<Node> Children => Enumerable.Empty<Node>();
  public override IEnumerable<Node> PreResolveChildren => Enumerable.Empty<Node>();
}