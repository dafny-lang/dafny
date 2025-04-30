using System.IO;
using System.Threading.Tasks;
using DafnyCore.Test;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;
using XunitAssertMessages;

namespace DafnyPipeline.Test {
  [Collection("Singleton Test Collection - Resolution")]

  public class RelativePaths {
    private readonly TextWriter output;

    public RelativePaths(ITestOutputHelper output) {
      this.output = new WriterFromOutputHelper(output);
    }

    [Fact]
    public async Task Test() {
      var exitCode = await DafnyBackwardsCompatibleCli.MainWithWriters(output, output,
        TextReader.Null, ["build", "--spill-translation", "testFile2.dfy"]);
      AssertM.Equal(0, exitCode, output.ToString());
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
