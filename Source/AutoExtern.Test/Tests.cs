using System.Diagnostics;
using Xunit;
using XUnitExtensions;

namespace AutoExtern.Test;

public class IntegrationTests {

  /// <summary>
  /// Translate <c>Minimal/Library.cs</c> and check the output.
  /// </summary>
  [Fact]
  public void MinimalTest() {
    var minimalDirectory = Path.GetFullPath("Minimal/");

    var startInfo = new ProcessStartInfo("dotnet") {
      UseShellExecute = false,
      WorkingDirectory = minimalDirectory
    };

    startInfo.ArgumentList.Add("../AutoExtern.dll");

    startInfo.ArgumentList.Add("Library.csproj"); // Project file
    startInfo.ArgumentList.Add("NS"); // Namespace
    startInfo.ArgumentList.Add("Library.dfy.template"); // Template
    startInfo.ArgumentList.Add("CSharpModel.dfy"); // Target for CSharpModel.dfy
    startInfo.ArgumentList.Add("--skip-interface");
    startInfo.ArgumentList.Add("NS.ICanClone");
    startInfo.ArgumentList.Add("Library.dfy"); // Target file
    startInfo.ArgumentList.Add("Library1.cs"); // Source file
    startInfo.ArgumentList.Add("Library2.cs"); // Source file
    startInfo.ArgumentList.Add("Library3.cs"); // Source file

    var dotnet = Process.Start(startInfo);

    Assert.NotNull(dotnet);
    Debug.Assert(dotnet != null);

    dotnet.WaitForExit();
    Assert.Equal(0, dotnet.ExitCode);

    var actualOutput = File.ReadAllText(Path.Join(minimalDirectory, "Library.dfy"));
    var expectedOutput = File.ReadAllText(Path.Join(minimalDirectory, "Library.dfy.expect"));
    AssertWithDiff.Equal(expectedOutput, actualOutput);
  }

  /// <summary>
  /// Run <c>make</c> in Tests/tutorial/AutoExtern and check the output.
  /// This is not done as a lit test because we use lit tests to test Dafny releases, and this
  /// tool is not part of Dafny releases.
  /// </summary>
  [Fact]
  public void ClientAppTest() {
    var tutorialDirectory = Path.GetFullPath("Tutorial/ClientApp");
    var expectedOutput = File.ReadAllText(Path.Join(tutorialDirectory, "GroceryListPrinter.dfy.expect"));

    Process? Make(IEnumerable<string> args) {
      var startInfo = new ProcessStartInfo("make") {
        RedirectStandardOutput = true,
        UseShellExecute = false
      };
      foreach (var arg in args) {
        startInfo.ArgumentList.Add(arg);
      }
      return Process.Start(startInfo);
    }

    var makeArgs = new[] { "--quiet", "-C", tutorialDirectory };

    // Ensure clean build
    Make(makeArgs.Concat(new[] { "clean" }))?.WaitForExit();

    // Run and capture output
    var run = Make(makeArgs.Concat(new[] {
      "AutoExtern=dotnet ../../AutoExtern.dll",
      "Dafny=dotnet ../../Dafny.dll"
    }));

    Assert.NotNull(run);
    Debug.Assert(run != null);

    var actualOutput = run.StandardOutput.ReadToEnd();
    AssertWithDiff.Equal(expectedOutput.ReplaceLineEndings(), actualOutput.ReplaceLineEndings());

    run.WaitForExit();
    Assert.Equal(0, run.ExitCode);
  }
}
