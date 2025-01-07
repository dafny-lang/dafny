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
    public static readonly bool UpdateExpectFile = "true" == Environment.GetEnvironmentVariable("DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE");

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
        if (Path.GetExtension(expectedOutputFile) == ".tmp") {
          return "With DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE=true, first argument of %diff cannot be a *.tmp file, it should be an *.expect file";
        }
        var path = Path.GetFullPath(expectedOutputFile).Replace("bin" + Path.DirectorySeparatorChar + "Debug" + Path.DirectorySeparatorChar + "net8.0" + Path.DirectorySeparatorChar, "");
        File.WriteAllText(path, actualOutput);
        return null;
      }
      var expected = File.ReadAllText(expectedOutputFile);
      return AssertWithDiff.GetDiffMessage(expected, actualOutput);
    }

    public async Task<int> Execute(TextReader inputReader,
      TextWriter outputWriter, TextWriter errorWriter) {
      var actual = await File.ReadAllTextAsync(ActualPath);
      var diffMessage = Run(ExpectedPath, actual);
      if (diffMessage != null) {
        await outputWriter.WriteAsync(diffMessage);
        return 1;
      }

      return 0;
    }

    public override string ToString() {
      return $"DiffCommand {ExpectedPath} {ActualPath}";
    }
  }
}