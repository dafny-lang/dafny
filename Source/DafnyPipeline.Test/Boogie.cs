using System;
using System.Diagnostics;
using System.IO;
using System.Text;
using DiffPlex.DiffBuilder;
using DiffPlex.DiffBuilder.Model;
using JetBrains.Annotations;
using Microsoft.Dafny;
using Xunit;

namespace DafnyPipeline.Test
{
    public class Boogie
    {
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
          Assert.Equal(expectedDiff, diff);
        }

        string GetDiff(string before, string after) {
          var diff = InlineDiffBuilder.Diff(before, after);
          var result = new StringBuilder();
          foreach (var line in diff.Lines)
          {
            switch (line.Type)
            {
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

        const string defaultDafnyArgs =
          "dotnet run --no-build --project /Users/rwillems/Documents/SourceCode/dafny/Source/DafnyDriver/DafnyDriver.csproj -- -useBaseNameForFileName -countVerificationErrors:0 -compileVerbose:0 /errorTrace:0";
        string GetBoogie(string dafnyProgram, [CanBeNull] string optionalFileName = null) {
          string fileName = optionalFileName ?? Path.GetTempFileName() + ".dfy";
          var writer  = File.CreateText(fileName);
          writer.Write(dafnyProgram);
          writer.Flush();
          var processStartInfo = new ProcessStartInfo
          {
            FileName = "dotnet",
            Arguments = $"{defaultDafnyArgs} /compile:0 /env:0 /print:- {fileName}",
            RedirectStandardOutput = true,
            UseShellExecute = false
          };
          var dafnyProcess = Process.Start(processStartInfo);
          var result = dafnyProcess.StandardOutput.ReadToEnd();
          dafnyProcess.WaitForExit();
          return result;
        }
    }
}
