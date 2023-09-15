using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using DafnyCore.Test;
using DafnyTestGeneration;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;
using BoogieProgram = Microsoft.Boogie.Program;

namespace DafnyPipeline.Test {
  // Main.Resolve has static shared state (TypeConstraint.ErrorsToBeReported for example)
  // so we can't execute tests that use it in parallel.
  [Collection("Singleton Test Collection - Resolution")]
  public class ProverLogStabilityTest {

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

    public ProverLogStabilityTest(ITestOutputHelper testOutputHelper) {
      this.testOutputHelper = testOutputHelper;
    }

    [Fact]
    public async Task ProverLogRegression() {
      var options = DafnyOptions.Create(new WriterFromOutputHelper(testOutputHelper));
      options.ProcsToCheck.Add("SomeMethod*");

      var filePath = Path.Combine(Directory.GetCurrentDirectory(), "expectedProverLog.txt");
      var expectation = await File.ReadAllTextAsync(filePath);
      var regularProverLog = await GetProverLogForProgramAsync(options, GetBoogie(options, originalProgram));
      Assert.Equal(expectation, regularProverLog.Replace("\r", ""));
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
      options.ProverLogFilePath = temp1;
      using (var engine = ExecutionEngine.CreateWithoutSharedCache(options)) {
        foreach (var boogieProgram in boogiePrograms) {
          var (outcome, _) = await DafnyMain.BoogieOnce(options, options.OutputWriter, engine, "", "", boogieProgram, "programId");
        }
      }
      foreach (var proverFile in Directory.GetFiles(directory)) {
        yield return await File.ReadAllTextAsync(proverFile);
      }
    }

    IEnumerable<BoogieProgram> GetBoogie(DafnyOptions options, string dafnyProgramText) {
      var reporter = new BatchErrorReporter(options);
      var dafnyProgram = Utils.Parse(reporter, dafnyProgramText, false);
      Assert.NotNull(dafnyProgram);
      DafnyMain.Resolve(dafnyProgram);
      Assert.Equal(0, reporter.ErrorCount);
      return Translator.Translate(dafnyProgram, reporter).Select(t => t.Item2).ToList();
    }
  }
}
