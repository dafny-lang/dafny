using System.Diagnostics;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.VisualStudio.TestPlatform.CommunicationUtilities.EventHandlers;
using Xunit.Abstractions;
using XUnitExtensions.Lit;

namespace IntegrationTests;

public class UpdateTests {
  
  public static async Task Main(string[] args) {
    Environment.SetEnvironmentVariable("DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE", "true");
    
    var files = Directory.GetFiles(args[0]);
    var key = "integration-tests";
    var integrationFiles = files.Where(f => {
      var fileName = Path.GetFileName(f);
      if (fileName.Length <= 2 + key.Length) {
        return false;
      }

      return fileName.Substring(2, key.Length) == key;

    });
    var failedTestNames = integrationFiles.SelectMany(file => {
      var content = File.ReadAllText(file);
      var regex = new Regex(@"Failed (.*) \[");
      var matches = regex.Matches(content);
      return matches.Select(m => m.Groups[1].Value);
    }).ToList();

    string? repoRoot = Directory.GetCurrentDirectory();
    while (repoRoot != null) {
      var currentFiles = Directory.GetDirectories(repoRoot);
      if (currentFiles.Any(f => Path.GetFileName(f) == ".git")) {
        break;
      }

      repoRoot = Path.GetDirectoryName(repoRoot)!;
    }

    var needsBuilds = true;
    for (var index = 0; index < failedTestNames.Count; index++) {
      Console.WriteLine($"Updating test {index+1}/{failedTestNames.Count}");
      var failedTestName = failedTestNames[index];
      var arguments = new List<string> { "test", $"name={failedTestName}", "update=true" };
      if (!needsBuilds) {
        arguments.Add("build=false");
      }
      needsBuilds = false;
      var process = Process.Start(
        new ProcessStartInfo("make", arguments) {
          RedirectStandardOutput = true,
          RedirectStandardError = true,
          WorkingDirectory = repoRoot,
        })!;
      var outputTask = process.StandardOutput.ReadToEndAsync();
      var errorTask = process.StandardError.ReadToEndAsync();
      await process.WaitForExitAsync();
      var output = await outputTask;
      var error = await errorTask;
      var exitCode = process.ExitCode;
    }
  }
}

class OutputHelper : ITestOutputHelper {
  public void WriteLine(string message) {
    throw new System.NotImplementedException();
  }

  public void WriteLine(string format, params object[] args) {
    throw new System.NotImplementedException();
  }
}