#nullable disable
using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class CoverageSpan : IComparable<CoverageSpan> {

  public readonly IOrigin Span;
  public readonly CoverageLabel Label;

  public CoverageSpan(IOrigin span, CoverageLabel label) {
    Contract.Assert(span.Uri != null);
    Contract.Assert(span.StartToken != null);
    Contract.Assert(span.EndToken != null);
    Span = span;
    Label = label;
  }

  public int CompareTo(CoverageSpan other) {
    return Span.StartToken.CompareTo(other.Span.StartToken);
  }
}