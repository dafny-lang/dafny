using System;
using System.IO;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions.Lit {
  public class DiffCommand : ILitCommand {

    private readonly string expectedPath;
    private readonly string actualPath;
    
    private DiffCommand(string expectedPath, string actualPath) {
      this.expectedPath = expectedPath;
      this.actualPath = actualPath;
    }

    public static ILitCommand Parse(string[] args) {
      if (args.Length != 2) {
        throw new ArgumentException($"Wrong number of arguments for diff: {args}");
      }
      var expectedPath = args[0];
      var actualPath = args[1];
      return new DiffCommand(expectedPath, actualPath);
    }
    
    public (int, string, string) Execute(ITestOutputHelper outputHelper, TextReader? inputReader, TextWriter? outputWriter, TextWriter? errorWriter) {
      var expected = File.ReadAllText(expectedPath);
      var actual = File.ReadAllText(actualPath);
      try {
        AssertWithDiff.Equal(expected, actual);
        return (0, "", "");
      } catch (AssertActualExpectedException e) {
        return (1, e.ToString(), "");
      }
    }

    public override string ToString() {
      return $"DiffCommand {expectedPath} {actualPath}";
    }
  }
}