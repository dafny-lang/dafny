using System.CommandLine;
using System.Diagnostics;
using System.IO.Compression;
using System.Text.RegularExpressions;

namespace IntegrationTests;

public class UpdateTests {

  public static Command GetCommand() {
    var result = new Command("update-expect-files", "Use the 'log archive' file downloaded from CI to update the integration tests");
    var fileArgument = new Argument<FileInfo>();
    result.AddArgument(fileArgument);
    result.SetHandler(file => Handle(file.Name), fileArgument);
    return result;
  }

  public static async Task Handle(string file) {
    Environment.SetEnvironmentVariable("DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE", "true");

    await using var zipFile = new FileStream(file, FileMode.Open);
    using var archive = new ZipArchive(zipFile, ZipArchiveMode.Read);
    var integrationFiles = archive.Entries.Where(entry => {
      var fileName = entry.Name;
      var regex = new Regex(@"\d+_integration-tests");
      var match = regex.Match(fileName);
      return match.Success;
    });
    var failedTestNames = integrationFiles.SelectMany(entry => {
      var content = new StreamReader(entry.Open()).ReadToEnd();
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

    Console.WriteLine($"Tests to update:\n{string.Join("\n", failedTestNames)}\n");

    var needsBuilds = true;
    for (var index = 0; index < failedTestNames.Count; index++) {
      var failedTestName = failedTestNames[index];
      Console.WriteLine($"Updating test {index + 1}/{failedTestNames.Count} '{failedTestName}'");
      var integrationTestsDir = $"{repoRoot}/Source/IntegrationTests";
      var arguments = new List<string> { "test", integrationTestsDir, $"--filter=DisplayName~{failedTestName}" };
      if (!needsBuilds) {
        arguments.Add("--no-build");
      }
      needsBuilds = false;
      var process = Process.Start(
        new ProcessStartInfo("dotnet", arguments) {
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
      if (exitCode != 0) {
        await Console.Error.WriteLineAsync($"Non-zero exit code. Output:\n{output}\nError:{error}");
        throw new Exception("Non-zero exit code");
      }
    }
  }
}