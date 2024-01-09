using System.Collections.Generic;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
public class MarkupTestFileTest {
  [Fact]
  public void AnnotatedSpan() {
    var input =
      @"Foo fi far (>here is some happy metadata::and the rest of it:::and now the text<) and the end of the program";
    MarkupTestFile.GetPositionsAndAnnotatedRanges(input, out var output, out _,
      out var ranges);

    var expectedOutput = @"Foo fi far and now the text and the end of the program";
    var expectedRanges = new List<AnnotatedRange> {
        new("here is some happy metadata::and the rest of it", new Range(0, 11, 0, 27))
      };
    Assert.Equal(expectedOutput, output);
    Assert.True(ranges.SequenceEqual(expectedRanges));
  }
}
