using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit;

namespace XUnitExtensions {
  public class LitTestCase {

    public static IEnumerable<LitCommandWithOutput> Read(string filePath, LitTestConfiguration config) {
      return File.ReadAllLines(filePath)
        .Select(line => ILitCommand.Parse(filePath, line, config))
        .Where(c => c != null);
    }
    
    public static void Run(string filePath, LitTestConfiguration config) {
      string fileName = Path.GetFileName(filePath);
      config = config.WithSubstitutions(new Dictionary<string, string> {
        { "%s", fileName },
        { "%t", Path.Join("Output", $"{fileName}.tmp")}
      });
      
      var commands = Read(filePath, config);
      foreach (var command in commands) {
        int exitCode;
        string output;
        string error;
        try {
          (exitCode, output, error) = command.Execute();
        } catch (Exception e) {
          throw new Exception($"Exception thrown while executing command: {command}", e);
        }
        Assert.True(exitCode == 0, $"Command failed with output:\n{output}\nError:\n{error}");
      }
    }
  }
}