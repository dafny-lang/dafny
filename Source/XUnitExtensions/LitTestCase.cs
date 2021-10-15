using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit;
using Xunit.Abstractions;

namespace XUnitExtensions {
  public class LitTestCase {

    private string filePath;
    private IEnumerable<ILitCommand> commands;
    private bool expectFailure;

    public static LitTestCase Read(string filePath, LitTestConfiguration config) {
      var commands = File.ReadAllLines(filePath)
        .Select(line => ILitCommand.Parse(filePath, line, config))
        .Where(c => c != null);
      var xfail = commands.Any(c => c is XFailCommand);
      return new LitTestCase(filePath, commands, xfail);
    }

    public static void Run(string filePath, LitTestConfiguration config, ITestOutputHelper outputHelper) {
      string fileName = Path.GetFileName(filePath);
      string directory = Path.GetDirectoryName(filePath);
      config = config.WithSubstitutions(new Dictionary<string, string> {
        { "%s", filePath },
        { "%S", directory },
        { "%t", Path.Join(directory, "Output", $"{fileName}.tmp")}
      });

      var testCase = Read(filePath, config);
      testCase.Execute(outputHelper);
    }

    public LitTestCase(string filePath, IEnumerable<ILitCommand> commands, bool expectFailure) {
      this.filePath = filePath;
      this.commands = commands;
      this.expectFailure = expectFailure;
    }

    public void Execute(ITestOutputHelper outputHelper) {
      Directory.CreateDirectory(Path.Join(Path.GetDirectoryName(filePath), "Output"));

      foreach (var command in commands) {
        int exitCode;
        string output;
        string error;
        try {
          outputHelper.WriteLine($"Executing command: {command}");
          (exitCode, output, error) = command.Execute(null, null, null);
        } catch (Exception e) {
          throw new Exception($"Exception thrown while executing command: {command}", e);
        }

        if (expectFailure) {
          if (exitCode != 0) {
            throw new SkipException($"Command returned non-zero exit code ({exitCode}): {command}\nOutput:\n{output}\nError:\n{error}");
          }
        }

        if (exitCode != 0) {
          throw new Exception($"Command returned non-zero exit code ({exitCode}): {command}\nOutput:\n{output}\nError:\n{error}");
        }
      }

      if (expectFailure) {
        throw new Exception($"Test case passed but expected to fail: {filePath}");
      }
    }
  }
}