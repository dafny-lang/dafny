using System;
using System.Diagnostics.Contracts;
using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace Microsoft.Dafny; 

public class CoverageSpan : IComparable<CoverageSpan> {

  public readonly RangeToken Span;
  public readonly CoverageLabel Label;
  internal static readonly Regex SpanRegexInverse = // used when parsing serialized coverage reports back to memory
    new("class=\"([a-z]+)\" id=\"line([0-9]+)col([0-9]+)-line([0-9]+)col([0-9]+)\"");

  public CoverageSpan(RangeToken span, CoverageLabel label) {
    Contract.Assert(span.Uri != null);
    Contract.Assert(span.StartToken != null);
    Contract.Assert(span.EndToken != null);
    Contract.Assert(span.StartToken.CompareTo(span.EndToken) != 0);
    Span = span;
    Label = label;
  }

  public int CompareTo(CoverageSpan other) {
    return Span.StartToken.CompareTo(other.Span.StartToken);
  }

  public string OpenHtmlTag() {
    var id = $"id=\"line{Span.StartToken.line}col{Span.StartToken.col}-line{Span.EndToken.line}col{Span.EndToken.col}\"";
    var classLabel = CoverageLabelExtension.ToHtmlClass(Label);
    return $"<span class=\"{classLabel}\" {id}>";
  }

  public string CloseHtmlTag() {
    return "</span>";
  }
}