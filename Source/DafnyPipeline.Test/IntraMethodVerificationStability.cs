using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore.Test;
using DafnyTestGeneration;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;
using BoogieProgram = Microsoft.Boogie.Program;
using Token = Microsoft.Boogie.Token;

namespace DafnyPipeline.Test {
  // Main.Resolve has static shared state (TypeConstraint.ErrorsToBeReported for example)
  // so we can't execute tests that use it in parallel.
  [Collection("Singleton Test Collection - Resolution")]
  public class IntraMethodVerificationStability {

    private readonly ITestOutputHelper testOutputHelper;

    // All types of top level declarations.
    readonly string originalProgram = @"
module SomeModule {

  module NestedModule {
    class C {
      var f: int
      constructor ()
    }
  }

  method m() {
    var x: NestedModule.C;
    x := new NestedModule.C();
    x.f := 4;
  }
}

import opened SomeModule

type FooSynonym<T> = FooClass

class FooClass {
  var f: int
  constructor ()
}

datatype Friends = Agnes | Agatha | Jermaine

function SomeFunc(funcFormal: int): nat { 3 }

method SomeMethod(methodFormal: int) returns (result: bool)
  requires methodFormal == 2
  ensures result == true 
  // ensures forall x :: x == methodFormal
{
  m();
  var lambdaExpr := x => x + 1;
  result := methodFormal == SomeFunc(42);
}
";

    readonly string renamedProgram = @"   

module SomeModule2 {

  module NestedModule2 {
      class C2 {
        var f2: int
        constructor ()
      }
    }

    method m2() {
      var x2: NestedModule2.C2;
      x2 := new NestedModule2.C2();
      x2.f2 := 4;
    }
}

import opened SomeModule2

type FooSynonym2<T> = FooClass2

class FooClass2 {
  var f: int
  constructor ()
}

datatype Friends2 = Agnes2 | Agatha2 | Jermaine2

function SomeFunc2(funcFormal: int): nat { 3 }

method SomeMethod2(methodFormal2: int) returns (result2: bool) 
  requires methodFormal2 == 2
  ensures result2 == true
  // ensures forall x :: x == methodFormal
{
  m2();
  var lambdaExpr2 := x => x + 1;
  result2 := methodFormal2 == SomeFunc2(42);
}
";

    readonly string reorderedProgram = @"
method SomeMethod(methodFormal: int) returns (result: bool)
  requires methodFormal == 2
  ensures result == true
  // ensures forall x :: x == methodFormal
{
  m();
  var lambdaExpr := x => x + 1;
  result := methodFormal == SomeFunc(42);
}

function SomeFunc(funcFormal: int): nat { 3 }

datatype Friends = Agnes | Agatha | Jermaine

class FooClass {
  var f: int
  constructor ()
}

type FooSynonym<T> = FooClass

import opened SomeModule

module SomeModule {

  module NestedModule {
    class C {
      var f: int
      constructor ()
    }
  }

  method m() {
    var x: NestedModule.C;
    x := new NestedModule.C();
    x.f := 4;
  }
}
";

    public IntraMethodVerificationStability(ITestOutputHelper testOutputHelper) {
      this.testOutputHelper = testOutputHelper;
    }

    [Fact]
    public async Task NoUniqueLinesWhenConcatenatingUnrelatedPrograms() {
      var options = DafnyOptions.CreateUsingOldParser((TextWriter)new WriterFromOutputHelper(testOutputHelper));
      Regex idAttributeRegex = new Regex("{:id \".*\"}");

      var regularBoogie = await GetBoogie(options, originalProgram);
      var renamedBoogie = await GetBoogie(options, renamedProgram);
      var regularBoogieText = idAttributeRegex.Replace(GetBoogieText(options, regularBoogie), "");
      var renamedBoogieText = idAttributeRegex.Replace(GetBoogieText(options, renamedBoogie), "");
      var separate = UniqueNonCommentLines(regularBoogieText + renamedBoogieText);
      var combinedBoogie = idAttributeRegex.Replace(GetBoogieText(options, await GetBoogie(options, originalProgram + renamedProgram)), "");
      var together = UniqueNonCommentLines(combinedBoogie);

      var uniqueLines = separate.Union(together).Except(separate.Intersect(together)).ToList();
      Assert.Equal(Enumerable.Empty<string>(), uniqueLines);
    }

    [Fact]
    public async Task EqualProverLogWhenReorderingProgram() {
      var options = DafnyOptions.CreateUsingOldParser((TextWriter)new WriterFromOutputHelper(testOutputHelper));
      options.ProcsToCheck.Add("SomeMethod*");

      var reorderedProverLog = await GetProverLogForProgramAsync(options, await GetBoogie(options, reorderedProgram));
      var regularProverLog = await GetProverLogForProgramAsync(options, await GetBoogie(options, originalProgram));
      Assert.Equal(regularProverLog, reorderedProverLog);
    }

    [Fact]
    public async Task EqualProverLogWhenRenamingProgram() {
      var options = DafnyOptions.CreateUsingOldParser((TextWriter)new WriterFromOutputHelper(testOutputHelper));
      options.ProcsToCheck.Add("*SomeMethod*");

      var renamedProverLog = await GetProverLogForProgramAsync(options, await GetBoogie(options, renamedProgram));
      var regularProverLog = await GetProverLogForProgramAsync(options, await GetBoogie(options, originalProgram));
      Assert.Equal(regularProverLog, renamedProverLog);
    }

    [Fact]
    public async Task EqualProverLogWhenAddingUnrelatedProgram() {

      var options = DafnyOptions.CreateUsingOldParser((TextWriter)new WriterFromOutputHelper(testOutputHelper));
      options.ProcsToCheck.Add("*SomeMethod *");

      var renamedProverLog = await GetProverLogForProgramAsync(options, await GetBoogie(options, renamedProgram + originalProgram));
      var regularProverLog = await GetProverLogForProgramAsync(options, await GetBoogie(options, originalProgram));
      Assert.Equal(regularProverLog, renamedProverLog);
    }

    private async Task<string> GetProverLogForProgramAsync(DafnyOptions options, IEnumerable<Microsoft.Boogie.Program> boogiePrograms) {
      var logs = await GetProverLogsForProgramAsync(options, boogiePrograms).ToListAsync();
      Assert.Single(logs);
      return logs[0];
    }

    private async IAsyncEnumerable<string> GetProverLogsForProgramAsync(DafnyOptions options,
      IEnumerable<BoogieProgram> boogiePrograms) {
      string directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
      Directory.CreateDirectory(directory);
      var temp1 = directory + "/proverLog";
      testOutputHelper.WriteLine("proverLog: " + temp1);
      options.ProverLogFilePath = temp1;
      options.ProcessSolverOptions(new ErrorReporterSink(options), Microsoft.Dafny.Token.NoToken);
      using (var engine = ExecutionEngine.CreateWithoutSharedCache(options)) {
        foreach (var boogieProgram in boogiePrograms) {
          var (outcome, _) = await DafnyMain.BoogieOnce(new ErrorReporterSink(options),
            options, new StringWriter(), engine, "", "", boogieProgram, "programId");
          testOutputHelper.WriteLine("outcome: " + outcome);
        }
      }
      foreach (var proverFile in Directory.GetFiles(directory)) {
        yield return await File.ReadAllTextAsync(proverFile);
      }
      Directory.Delete(directory, true);
    }

    ISet<string> UniqueNonCommentLines(string input) {
      return input.Split('\n').Where(line => !line.TrimStart().StartsWith("//")).ToHashSet();
    }

    string PrintBoogie(CoreOptions options, BoogieProgram program) {
      var result = new StringWriter();
      var writer = new TokenTextWriter(result, options);
      program.Emit(writer);
      return result.ToString();
    }

    string GetBoogieText(CoreOptions options, IEnumerable<BoogieProgram> boogieProgram) {
      return string.Join('\n', boogieProgram.Select(x => PrintBoogie(options, x)));
    }

    async Task<IReadOnlyList<BoogieProgram>> GetBoogie(DafnyOptions options, string dafnyProgramText) {
      var reporter = new BatchErrorReporter(options);
      var dafnyProgram = await Utils.Parse(reporter, dafnyProgramText, false);
      Assert.NotNull(dafnyProgram);
      DafnyMain.Resolve(dafnyProgram);
      Assert.Equal(0, reporter.ErrorCount);
      return BoogieGenerator.Translate(dafnyProgram, reporter).Select(t => t.Item2).ToList();
    }
  }
}
