using System.IO;
using Xunit;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class DiffCommand : ILitCommand {

    private readonly string expectedPath;
    private readonly string actualPath;
    
    private DiffCommand(string expectedPath, string actualPath) {
      this.expectedPath = expectedPath;
      this.actualPath = actualPath;
    }

    public static ILitCommand Parse(string[] args) {
      var expectedPath = args[0];
      var actualPath = args[1];
      return new DiffCommand(expectedPath, actualPath);
    }
    
    public (int, string, string) Execute(ITestOutputHelper outputHelper, TextReader? inputReader, TextWriter? outputWriter, TextWriter? errorWriter) {
      var expected = File.ReadAllText(expectedPath);
      var actual = File.ReadAllText(actualPath);
      AssertWithDiff.Equal(expected, actual);
      return (0, "", "");
    }

    public override string ToString() {
      return $"DiffCommand {expectedPath} {actualPath}";
    }
  }
}