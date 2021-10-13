using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit;
using Xunit.Abstractions;

namespace XUnitExtensions {
  public class LitTestCase {

    public static IEnumerable<LitCommandWithOutput> Read(string filePath, LitTestConfiguration config) {
      return File.ReadAllLines(filePath)
        .Select(line => ILitCommand.Parse(filePath, line, config))
        .Where(c => c != null);
    }
    
    public static void Run(string filePath, LitTestConfiguration config, ITestOutputHelper outputHelper) {
      string fileName = Path.GetFileName(filePath);
      string directory = Path.GetDirectoryName(filePath);
      config = config.WithSubstitutions(new Dictionary<string, string> {
        { "%s", filePath },
        { "%S", directory },
        { "%t", Path.Join(directory, "Output", $"{fileName}.tmp")}
      });

      Directory.CreateDirectory(Path.Join(directory, "Output"));
      
      var commands = Read(filePath, config);
      foreach (var command in commands) {
        int exitCode;
        string output;
        string error;
        try {
          outputHelper.WriteLine($"Executing command: {command}");
          (exitCode, output, error) = command.Execute();
        } catch (Exception e) {
          throw new Exception($"Exception thrown while executing command: {command}", e);
        }

        if (exitCode != 0) {
          throw new Exception($"Command returned non-zero exit code ({exitCode}): {command}\nOutput:\n{output}\nError:\n{error}");
        }
      }
    }
  }
}