using System.Collections;
using System.Collections.Generic;
using System.Linq;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util; 
[TestClass]
public class MarkupTestFileTest {
  [TestMethod]
  public void AnnotatedSpan() {
    var input =
      @"Foo fi far |>here is some happy metadata::and the rest of it|||and now the text<| and the end of the program";
      MarkupTestFile.GetPositionsAndNamedRanges(input, out var output, out _,
        out var ranges);

      var expectedOutput = @"Foo fi far and now the text and the end of the program";
      var expectedRanges = new Dictionary<string, Range>() {
        {"here is some happy metadata::and the rest of it", new Range(0, 11, 0, 27)}
      };
      Assert.AreEqual(expectedOutput, output);
      Assert.IsTrue(ranges.Select(r => KeyValuePair.Create(r.Key, r.Value[0])).SequenceEqual(expectedRanges));
  }
}