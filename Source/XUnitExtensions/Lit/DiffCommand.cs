using System;
using System.IO;
using System.Threading.Tasks;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions.Lit {
  /// <summary>
  /// This class implements the equivalent of the Unix 'diff' command that lit tests rely on,
  /// because 'diff' does not exist on Windows.
  /// </summary>
  public class DiffCommand : ILitCommand {
    public static readonly bool UpdateExpectFile = false;

    public string ExpectedPath { get; }
    public string ActualPath { get; }

    private DiffCommand(string expectedPath, string actualPath) {
      ExpectedPath = expectedPath;
      ActualPath = actualPath;
    }

    public static ILitCommand Parse(string[] args) {
      if (args.Length != 2) {
        throw new ArgumentException($"Wrong number of arguments for diff: {args}");
      }
      var expectedPath = args[0];
      var actualPath = args[1];
      return new DiffCommand(expectedPath, actualPath);
    }

    public static string? Run(string expectedOutputFile, string actualOutput) {
      if (UpdateExpectFile) {
        var path = Path.GetFullPath(expectedOutputFile).Replace("bin/Debug/net6.0/", "");
        File.WriteAllText(path, actualOutput);
        return null;
      }
      var expected = File.ReadAllText(expectedOutputFile);
      return AssertWithDiff.GetDiffMessage(expected, actualOutput);
    }

    public Task<int> Execute(TextReader inputReader,
      TextWriter outputWriter, TextWriter errorWriter) {
      var actual = File.ReadAllText(ActualPath);
      var diffMessage = Run(ExpectedPath, actual);
      if (diffMessage != null) {
        outputWriter.Write(diffMessage);
        return Task.FromResult(1);
      }

      return Task.FromResult(0);
    }

    public override string ToString() {
      return $"DiffCommand {ExpectedPath} {ActualPath}";
    }
  }
}