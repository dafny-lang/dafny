using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class LitTestCase {
    public string FilePath { get; }
    public IEnumerable<ILitCommand> Commands { get; }
    public bool ExpectFailure { get; }

    private static LitTestCase Parse(string filePath, LitTestConfiguration config) {
      ILitCommand[] commands = File.ReadAllLines(filePath)
        .Select(line => ILitCommand.Parse(line, config))
        .Where(c => c != null)
        .Select(e => e!)
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

    public static LitTestCase Read(string filePath, LitTestConfiguration config) {
      string fileName = Path.GetFileName(filePath);
      string? directory = Path.GetDirectoryName(filePath);
      if (directory == null) {
        throw new ArgumentException($"Couldn't get directory name for path: {filePath}");
      }

      string fullDirectoryPath = Path.GetFullPath(directory).Replace(@"\", "/");
      config = config.WithSubstitutions(new Dictionary<string, object> {
        {"%s", filePath.Replace(@"\", "/")},
        // For class path separators
        {"%{pathsep}", Path.PathSeparator.ToString()},
        {"%S", fullDirectoryPath},
        {"%t", Path.Join(fullDirectoryPath, "Output", $"{fileName}.tmp")}
      });

      return Parse(filePath, config);
    }

    public static void Run(string filePath, LitTestConfiguration config, ITestOutputHelper outputHelper) {
      Read(filePath, config).Execute(outputHelper);
    }

    public LitTestCase(string filePath, IEnumerable<ILitCommand> commands, bool expectFailure) {
      this.FilePath = filePath;
      this.Commands = commands;
      this.ExpectFailure = expectFailure;
    }

    public void Execute(ITestOutputHelper outputHelper) {
      Directory.CreateDirectory(Path.Join(Path.GetDirectoryName(FilePath), "Output"));
      // For debugging. Only printed on failure in case the true cause is buried in an earlier command.
      List<(string, string)> results = new();

      foreach (var command in Commands) {
        int exitCode;
        string output;
        string error;
        var outputWriter = new StringWriter();
        var errorWriter = new StringWriter();
        try {
          outputHelper.WriteLine($"Executing command: {command}");
          (exitCode, output, error) = command.Execute(TextReader.Null, outputWriter, errorWriter);
        } catch (Exception e) {
          throw new Exception($"Exception thrown while executing command: {command}", e);
        }

        if (ExpectFailure) {
          if (exitCode != 0) {
            throw new SkipException(
              $"Command returned non-zero exit code ({exitCode}): {command}\nOutput:\n{output + outputWriter}\nError:\n{error + errorWriter}");
          }
        }

        if (exitCode != 0) {
          outputHelper?.WriteLine("Previous command results:");
          foreach (var (prevOutput, prevError) in results) {
            outputHelper?.WriteLine($"Output:\n{prevOutput}");
            outputHelper?.WriteLine($"Error:\n{prevError}");
          }

          throw new Exception(
            $"Command returned non-zero exit code ({exitCode}): {command}\nOutput:\n{output + outputWriter}\nError:\n{error + errorWriter}");
        }

        results.Add((output, error));
      }

      if (ExpectFailure) {
        throw new Exception($"Test case passed but expected to fail: {FilePath}");
      }
    }
  }
}