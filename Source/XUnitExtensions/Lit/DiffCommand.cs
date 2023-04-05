using System;
using System.IO;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions.Lit {
  /// <summary>
  /// This class implements the equivalent of the Unix 'diff' command that lit tests rely on,
  /// because 'diff' does not exist on Windows.
  /// </summary>
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

    public (int, string, string) Execute(TextReader? inputReader,
      TextWriter? outputWriter, TextWriter? errorWriter) {
      var expected = File.ReadAllText(expectedPath);
      var actual = File.ReadAllText(actualPath);
      var diffMessage = AssertWithDiff.GetDiffMessage(expected, actual);
      return diffMessage == null ? (0, "", "") : (1, diffMessage, "");
    }

    public override string ToString() {
      return $"DiffCommand {expectedPath} {actualPath}";
    }
  }
}