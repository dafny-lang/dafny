using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class LitTestCase {

    private readonly string filePath;
    private readonly IEnumerable<ILitCommand> commands;
    private readonly bool expectFailure;

    public static LitTestCase Read(string filePath, LitTestConfiguration config) {
      var commands = File.ReadAllLines(filePath)
        .Select(line => ILitCommand.Parse(line, config))
        .Where(c => c != null)
        .ToArray();
      if (commands.Length == 0) {
        throw new ArgumentException($"No lit commands found in test file: {filePath}");
      }
      var xfail = commands.Any(c => c is XFailCommand);
      foreach (var unsupported in commands.OfType<UnsupportedCommand>()) {
        foreach (var feature in config.Features) {
          if (unsupported.Features.Contains(feature)) {
            throw new SkipException($"Test case not supported: {feature}");
          }
        }
      }
      return new LitTestCase(filePath, commands, xfail);
    }

    public static void Run(string filePath, LitTestConfiguration config, ITestOutputHelper outputHelper) {
      string fileName = Path.GetFileName(filePath);
      string? directory = Path.GetDirectoryName(filePath);
      if (directory == null) {
        throw new ArgumentException("Couldn't get directory name for path: {}");
      }
      string fullDirectoryPath = Path.GetFullPath(directory);
      config = config.WithSubstitutions(new Dictionary<string, string> {
        { "%s", filePath },
        { "%S", fullDirectoryPath },
        { "%t", Path.Join(fullDirectoryPath, "Output", $"{fileName}.tmp")}
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
          (exitCode, output, error) = command.Execute(outputHelper, null, null, null);
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