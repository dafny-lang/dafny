using System.IO;
using Microsoft.Dafny;
using Xunit;

namespace DafnyPipeline.Test {
  [Collection("Singleton Test Collection - Resolution")]

  public class RelativePaths {
    [Fact]
    public void Test() {
      Assert.Equal(0, DafnyDriver.ThreadMain(new string[] { "/spillTargetCode:3", "warnings-as-errors.dfy" }));
    }

    [Fact]
    public void TestFileConversion() {
      var filePath = @"file:\c:\Users\xxx\Documents\with%20space\test.dfy";
      var filePath1 = @"file:c:\Users\xxx\Documents\with%20space\test.dfy";
      var expected = @"c:\Users\xxx\Documents\with space\test.dfy";
      Assert.Equal(expected, DafnyFile.Canonicalize(filePath));
      Assert.Equal(expected, DafnyFile.Canonicalize(filePath1));
    }
  }
}