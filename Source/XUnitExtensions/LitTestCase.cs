using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit;

namespace XUnitExtensions {
  public class LitTestCase {

    public static IEnumerable<ILitCommand> Read(string filePath, LitTestConfiguration config) {
      return File.ReadAllLines(filePath)
        .Select(line => ILitCommand.Parse(line, config))
        .Where(c => c != null);
    }
    
    public static void Run(string filePath, LitTestConfiguration config) {
      string directory = Path.GetDirectoryName(filePath);
      config = config.WithSubsitutions(new Dictionary<string, string> {
        { "%s", filePath },
        { "%t", Path.Join(directory, "Output", $"{Path.GetFileName(filePath)}.tmp")}
      });
      
      // TODO: apply this for %dafny and any other commands where we recognize file arguments
      // Lit always uses the parent directory of a test file as the current directory,
      // but xUnit tests will always use the .NET output directory,
      // so other file paths have to be interpreted to be relative to the .NET output directory instead.
      // otherFiles.Add(Path.Join(Path.GetDirectoryName(filePath), value));
      var commands = Read(filePath, config);
      foreach (var command in commands) {
        try {
          var (exitCode, output, error) = command.Execute();
          Assert.True(exitCode == 0, $"Command failed with output:\n{output}\nError:\n{error}");
        } catch (Exception e) {
          throw new Exception($"Exception thrown while executing command: {command}", e);
        }
      }
    }
  }
}