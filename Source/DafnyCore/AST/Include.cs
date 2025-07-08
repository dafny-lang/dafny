using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class Include : NodeWithOrigin, IComparable {
  public DafnyOptions ParseOptions { get; }
  public Uri IncluderFilename { get; }
  public Uri IncludedFilename { get; }
  public string CanonicalPath { get; }

  public Include(IOrigin origin, Uri includer, Uri theFilename, DafnyOptions parseOptions) : base(origin) {
    this.IncluderFilename = includer;
    this.IncludedFilename = theFilename;
    ParseOptions = parseOptions;
    this.CanonicalPath = DafnyFile.Canonicalize(theFilename.LocalPath).LocalPath;
  }

  public IOrigin PathOrigin => new SourceOrigin(ReportingRange.StartToken, EndToken);

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