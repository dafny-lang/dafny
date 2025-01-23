using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class Include(IOrigin origin, Uri includer, Uri theFilename, DafnyOptions parseOptions)
  : NodeWithComputedRange(origin), IComparable {
  public DafnyOptions ParseOptions { get; } = parseOptions;
  public Uri IncluderFilename { get; } = includer;
  public Uri IncludedFilename { get; } = theFilename;
  public string CanonicalPath { get; } = DafnyFile.Canonicalize(theFilename.LocalPath).LocalPath;

  public IOrigin PathOrigin => new SourceOrigin(Center, EndToken);

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