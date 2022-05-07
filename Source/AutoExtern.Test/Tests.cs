using System.Diagnostics;
using Microsoft.Build.Evaluation;
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
      WorkingDirectory = minimalDirectory,
    };

    startInfo.ArgumentList.Add("../AutoExtern.dll");

    startInfo.ArgumentList.Add("Library.csproj"); // Project file
    startInfo.ArgumentList.Add("Library.cs"); // Source file
    startInfo.ArgumentList.Add("NS"); // Namespace
    startInfo.ArgumentList.Add("Library.dfy.template"); // Template
    startInfo.ArgumentList.Add("CSharpModel.dfy"); // Target for CSharpModel.dfy
    startInfo.ArgumentList.Add("Library.dfy"); // Target file

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

    var startInfo = new ProcessStartInfo("make") {
      RedirectStandardOutput = true,
      UseShellExecute = false
    };

    startInfo.ArgumentList.Add("--quiet");
    startInfo.ArgumentList.Add("-C");
    startInfo.ArgumentList.Add(tutorialDirectory);
    startInfo.ArgumentList.Add($"AutoExtern=dotnet ../../AutoExtern.dll");
    var make = Process.Start(startInfo);

    Assert.NotNull(make);
    Debug.Assert(make != null);

    var actualOutput = make.StandardOutput.ReadToEnd();
    AssertWithDiff.Equal(expectedOutput.ReplaceLineEndings(), actualOutput.ReplaceLineEndings());

    make.WaitForExit();
    Assert.Equal(0, make.ExitCode);
  }
}
