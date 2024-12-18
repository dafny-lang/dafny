using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class Include : TokenNode, IComparable {
  public DafnyOptions ParseOptions { get; }
  public Uri IncluderFilename { get; }
  public Uri IncludedFilename { get; }
  public string CanonicalPath { get; }

  public Include(IOrigin tok, Uri includer, Uri theFilename, DafnyOptions parseOptions) {
    this.tok = tok;
    this.IncluderFilename = includer;
    this.IncludedFilename = theFilename;
    ParseOptions = parseOptions;
    this.CanonicalPath = DafnyFile.Canonicalize(theFilename.LocalPath).LocalPath;
  }

  public int CompareTo(object obj) {
    if (obj is Include include) {
      return CanonicalPath.CompareTo(include.CanonicalPath);
    } else {
      throw new NotImplementedException();
    }
  }

  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();
  public override IEnumerable<INode> PreResolveChildren => Enumerable.Empty<Node>();
}