using System.IO;
using Microsoft.Dafny;
using Xunit;

namespace DafnyPipeline.Test {
  [Collection("Singleton Test Collection - Resolution")]

  public class RelativePaths {
    [Fact]
    public void Test() {
      Directory.SetCurrentDirectory(Path.Join("TestFiles", "LitTests", "LitTest"));
      var code = DafnyDriver.ThreadMain(new string[] { "/spillTargetCode:3", "warnings-as-errors.dfy" });
      Directory.SetCurrentDirectory(Path.Join("..", "..", ".."));
      Assert.Equal(0, code);
    }
  }
}