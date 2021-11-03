using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;
using BoogieProgram = Microsoft.Boogie.Program;
using Parser = Microsoft.Dafny.Parser;
using Type = System.Type;

namespace DafnyPipeline.Test {
  // Main.Resolve has static shared state (TypeConstraint.ErrorsToBeReported for example)
  // so we can't execute tests that use it in parallel.
  [Collection("Singleton Test Collection - Resolution")]
  public class IntraMethodVerificationStability {
    private readonly ITestOutputHelper testOutputHelper;

    // All types of top level declarations.
    // But also all types of AST nodes, they may all generate something using counters.
    // Just trying to come up with this very large Dafny program is a hassle. Would be awesome if it could be generated based on the types.

    readonly string originalProgram = $@"
module SomeModule {{

  module NestedModule {{
    class C {{
      var f: int
      constructor ()
    }}
  }}

  method m() {{
    var x: NestedModule.C;
    x := new NestedModule.C();
    x.f := 4;
  }}
}}

import opened SomeModule

type FooSynonym<T> = FooClass

class FooClass {{
  var f: int
  constructor ()
}}

datatype Friends = Agnes | Agatha | Jermaine

function method SomeFunc(funcFormal: int): nat {{ 3 }}

method SomeMethod(methodFormal: int) returns (result: bool)
  requires methodFormal == 2
  ensures result == true 
  // ensures forall x :: x == methodFormal
{{
  m();
  var lambdaExpr := x => x + 1;
  result := methodFormal == SomeFunc(42);
}}
";

    readonly string renamedProgram = $@"   

module SomeModule2 {{

  module NestedModule {{
      class C {{
        var f: int
        constructor ()
      }}
    }}

    method m() {{
      var x: NestedModule.C;
      x := new NestedModule.C();
      x.f := 4;
    }}
}}

type FooSynonym2<T> = FooClass2

class FooClass2 {{
  var f: int
  constructor ()
}}

datatype Friends2 = Agnes2 | Agatha2 | Jermaine2

function method SomeFunc2(funcFormal: int): nat {{ 3 }}

method SomeMethod2(methodFormal: int) returns (result: bool) 
  requires methodFormal == 2
  ensures result == true
  // ensures forall x :: x == methodFormal
{{
  var lambdaExpr := x => x + 1;
  result := methodFormal == SomeFunc2(42);
}}
";

    public IntraMethodVerificationStability(ITestOutputHelper testOutputHelper) {
      this.testOutputHelper = testOutputHelper;
    }

    [Fact]
    public void NoUniqueLinesWhenConcatenatingUnrelatedPrograms() {
      DafnyOptions.Install(new DafnyOptions());

      var regularBoogie = GetBoogie(originalProgram).ToList();
      var renamedBoogie = GetBoogie(renamedProgram).ToList();
      var regularBoogieText = GetBoogieText(regularBoogie);
      var renamedBoogieText = GetBoogieText(renamedBoogie);
      var separate = UniqueNonCommentLines(regularBoogieText + renamedBoogieText);
      var combinedBoogie = GetBoogieText(GetBoogie(originalProgram + renamedProgram));
      var together = UniqueNonCommentLines(combinedBoogie);

      var uniqueLines = separate.Union(together).Except(separate.Intersect(together)).ToList();
      Assert.Equal(Enumerable.Empty<string>(), uniqueLines);
    }

    // Inter method proof isolation.
    [Fact]
    public void NoUniqueLinesWhenConcatenatingUnrelatedBlocks() {
      // TODO
    }

    [Fact]
    public void EqualProverLogWhenAddingUnrelatedProgram() {

      DafnyOptions.Install(new DafnyOptions());
      CommandLineOptions.Clo.Parse(new [] {""});
      CommandLineOptions.Clo.ProcsToCheck.Add("*SomeMethod");
      ExecutionEngine.printer = new ConsolePrinter(); // For boogie errors

      var regularProverLog = GetProverLogsForProgram(GetBoogie(originalProgram)).ToList();
      var renamedProverLog = GetProverLogsForProgram(GetBoogie(renamedProgram + originalProgram)).ToList();
      Assert.Equal(regularProverLog, renamedProverLog);
    }

    private string GetProverLogForProgram(IEnumerable<Microsoft.Boogie.Program> boogiePrograms) {
      var logs = GetProverLogsForProgram(boogiePrograms).ToList();
      Assert.Single(logs);
      return logs[0];
    }
    
    private IEnumerable<string> GetProverLogsForProgram(IEnumerable<Microsoft.Boogie.Program> boogiePrograms)
    {
      string directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
      Directory.CreateDirectory(directory);
      var temp1 = directory + "/proverLog";
      testOutputHelper.WriteLine("proverLog: " + temp1);
      CommandLineOptions.Clo.ProverLogFilePath = temp1;
      foreach (var boogieProgram in boogiePrograms) {
        Main.BoogieOnce("", "", boogieProgram, "programId", out var stats, out var outcome);
        testOutputHelper.WriteLine("outcome: " + outcome);
        foreach (var proverFile in Directory.GetFiles(directory)) {
          yield return File.ReadAllText(proverFile);
        }
      }
    }
    
    ISet<string> UniqueNonCommentLines(string input) {
      return input.Split('\n').Where(line => !line.TrimStart().StartsWith("//")).ToHashSet();
    }

    string PrintBoogie(BoogieProgram program) {
      var result = new StringWriter();
      var writer = new TokenTextWriter(result);
      program.Emit(writer);
      return result.ToString();
    }

    string GetBoogieText(IEnumerable<BoogieProgram> boogieProgram) {
      return string.Join('\n', boogieProgram.Select(PrintBoogie));
    }

    IEnumerable<BoogieProgram> GetBoogie(string dafnyProgramText) {
      var module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
      var fullFilePath = "foo";
      Microsoft.Dafny.Type.ResetScopes();
      var builtIns = new BuiltIns();
      var errorReporter = new ConsoleErrorReporter();
      var parseResult = Parser.Parse(dafnyProgramText, fullFilePath, "foo", module, builtIns, errorReporter);
      Assert.Equal(0, parseResult);
      var dafnyProgram = new Microsoft.Dafny.Program(fullFilePath, module, builtIns, errorReporter);
      Main.Resolve(dafnyProgram, errorReporter);
      Assert.Equal(0, errorReporter.ErrorCount);
      var boogiePrograms = Translator.Translate(dafnyProgram, errorReporter).Select(t => t.Item2).ToList();
      var programTexts = boogiePrograms.Select(b => {
        var stringWriter = new StringWriter();
        b.Emit(new TokenTextWriter(stringWriter));
        return stringWriter.ToString();
      }).ToList();
      return boogiePrograms;
    }
  }


}