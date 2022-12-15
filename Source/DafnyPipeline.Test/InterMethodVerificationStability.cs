using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using DiffPlex.DiffBuilder;
using DiffPlex.DiffBuilder.Model;
using Microsoft.VisualStudio.TestPlatform.PlatformAbstractions;
using Xunit;

namespace DafnyPipeline.Test {
  // Main.Resolve has static shared state (TypeConstraint.ErrorsToBeReported for example)
  // so we can't execute tests that use it in parallel.
  [Collection("Singleton Test Collection - Resolution")]
  public class InterMethodVerificationStability {
    [Fact]
    public void CreatingBoogieVariableNameCollisionsHasExpectedDiff() {
      var beforeChange = @"
method M(heap: object) 
modifies heap
{
  var x := 0;
  if y :| y < x {
    var x := 0; 
  } else {
    var y := 0;
  }

  while(x < 5) {
    var x := 2;
    var y := 0;
  }

  for i: int := 0 to 3 {
    var x := 2;
    var y := 0;
  }

  forall i | 0 <= i < x {
    var x := 2;
    var y := 0;
  }

  var s := {2,3};
  modify heap {
    var z := 3; // modify does not push a Dafny scope, so we can't assign to a fresh x here.
  }

  assert x == 0 by {
    var x := x + 2;
    var y := 0;
  }
  var y := 200;
}";

      var afterChange = @"
method M(heap: object) 
  modifies heap
{
  var x := 0;
  if k :| k < x {
    var a := 0; 
  } else {
    var b := 0;
  }
  
  while(x < 5) {
    var c := 2;
    var d := 0;
  }
  
  for i: int := 0 to 3 {
    var e := 2;
    var f := 0;
  }
  
  forall i | 0 <= i < x {
    var g := 2;
    var h := 0;
  }
  
  var s := {2,3};
  modify heap {
    var z := 3; // modify does not push a Dafny scope, so we can't assign to a fresh x here.
  }
  
  assert x == 0 by {
    var i := x + 2;
    var j := 0;
  }
  var y := 200;
}";
      var tempPath = Path.GetTempFileName() + ".dfy";
      var beforeBoogie = GetBoogie(beforeChange, tempPath);
      var afterBoogie = GetBoogie(afterChange, tempPath);
      var diff = GetDiff(beforeBoogie, afterBoogie);

      var expectedDiff = @"-   var eg$y#0: int;
-   var y#0_0: int;
-   var x#1_0: int;
-   var y#2_0: int;
+   var eg$k#0: int;
+   var k#0_0: int;
+   var a#1_0: int;
+   var b#2_0: int;
-   var x#3_0: int;
-   var y#3_0: int;
+   var c#3_0: int;
+   var d#3_0: int;
-   var x#4_0: int;
-   var y#4_0: int;
+   var e#4_0: int;
+   var f#4_0: int;
-   var x#5_0: int;
-   var y#5_0: int;
+   var g#5_0: int;
+   var h#5_0: int;
-   var x#7_0: int;
-   var y#7_0: int;
+   var i#7_0: int;
+   var j#7_0: int;
-     havoc eg$y#0;
+     havoc eg$k#0;
-     havoc y#0_0;
+     havoc k#0_0;
-         assume y#0_0 < x#0;
+         assume k#0_0 < x#0;
-         x#1_0 := LitInt(0);
+         a#1_0 := LitInt(0);
-         assume !(exists eg$y#1: int :: eg$y#1 < x#0);
+         assume !(exists eg$k#1: int :: eg$k#1 < x#0);
-         y#2_0 := LitInt(0);
+         b#2_0 := LitInt(0);
-         x#3_0 := LitInt(2);
+         c#3_0 := LitInt(2);
-         y#3_0 := LitInt(0);
+         d#3_0 := LitInt(0);
-         x#4_0 := LitInt(2);
+         e#4_0 := LitInt(2);
-         y#4_0 := LitInt(0);
+         f#4_0 := LitInt(0);
-         x#5_0 := LitInt(2);
+         g#5_0 := LitInt(2);
-         y#5_0 := LitInt(0);
+         h#5_0 := LitInt(0);
-         x#7_0 := x#0 + 2;
+         i#7_0 := x#0 + 2;
-         y#7_0 := LitInt(0);
+         j#7_0 := LitInt(0);
";
      Assert.Equal(expectedDiff.Replace("\r\n", "\n"), diff.Replace("\r\n", "\n"));
    }

    string GetDiff(string before, string after) {
      var diff = InlineDiffBuilder.Diff(before, after);
      var result = new StringBuilder();
      foreach (var line in diff.Lines) {
        switch (line.Type) {
          case ChangeType.Inserted:
            result.Append("+ ");
            result.AppendLine(line.Text);
            break;
          case ChangeType.Deleted:
            result.Append("- ");
            result.AppendLine(line.Text);
            break;
        }
      }

      return result.ToString();
    }

    static InterMethodVerificationStability() {
      var testAssemblyPath = Assembly.GetAssembly(typeof(InterMethodVerificationStability)).GetAssemblyLocation();
      var parts = testAssemblyPath.Split(Path.DirectorySeparatorChar);
      // This way of finding the repository root is not reliable, we should instead reference the DafnyPipeline assembly and run Dafny in the same process as the unit tests.
      var sourceIndex = Array.FindLastIndex(parts, e => e == "Source");
      dafnyDirectory = Path.Combine(Path.GetPathRoot(testAssemblyPath)!, Path.Combine(parts.Take(sourceIndex).ToArray()));
      Console.WriteLine("dafnyDirectory: " + dafnyDirectory);
      Console.WriteLine("DafnyProjectFile: " + DafnyProjectFile);
    }

    private static readonly string dafnyDirectory;

    private static string DafnyProjectFile => Path.Combine(dafnyDirectory, "Source", "Dafny", "Dafny.csproj");
    private static string DefaultDafnyArgs => $"run --no-build --project {DafnyProjectFile} -- -useBaseNameForFileName -compileVerbose:0 /errorTrace:0";

    string GetBoogie(string dafnyProgram, string optionalFileName = null) {
      string fileName = optionalFileName ?? Path.GetTempFileName() + ".dfy";
      File.WriteAllText(fileName, dafnyProgram);
      var processStartInfo = new ProcessStartInfo {
        FileName = "dotnet",
        Arguments = $"{DefaultDafnyArgs} /compile:0 /env:0 /print:- {fileName}",
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        UseShellExecute = false
      };
      using var dafnyProcess = Process.Start(processStartInfo);
      var result = dafnyProcess.StandardOutput.ReadToEnd();
      dafnyProcess.WaitForExit();

      if (dafnyProcess.ExitCode != 0) {
        Console.Out.WriteLine("Arguments:", processStartInfo.Arguments);
        Console.Out.WriteLine("Result:");
        Console.Out.WriteLine(result);
        Console.Out.WriteLine(dafnyProcess.StandardError.ReadToEnd());
        Console.Out.Flush();
      }
      Assert.Equal(4, dafnyProcess.ExitCode);
      return result;
    }
  }
}
