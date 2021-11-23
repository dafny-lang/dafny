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
  }
}