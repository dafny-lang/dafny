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
    public void TestFileCanonicalization() {
      var filePath1 = @"file:\c:\Users\xxx\Documents\with%20space\test.dfy";
      var filePath2 = @"file:c:\Users\xxx\Documents\with%20space\test.dfy";
      var expected = @"c:\Users\xxx\Documents\with space\test.dfy";
      Assert.Equal(expected, DafnyFile.Canonicalize(filePath1).LocalPath);
      Assert.Equal(expected, DafnyFile.Canonicalize(filePath2).LocalPath);
      filePath1 = @"file:///home/dev/with%20space/test.dfy";
      filePath2 = @"file:/home/dev/with%20space/test.dfy";
      expected = @"/home/dev/with space/test.dfy";
      Assert.Equal(expected, DafnyFile.Canonicalize(filePath1).LocalPath);
      Assert.Equal(expected, DafnyFile.Canonicalize(filePath2).LocalPath);
    }
  }
}
