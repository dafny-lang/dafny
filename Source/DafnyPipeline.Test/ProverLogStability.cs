using System;
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

  method m() ensures false {
    var x: NestedModule.C;
    x := new NestedModule.C();
    x.f := 4;
  }
}

import opened SomeModule

type FooSynonym<T> = FooClass

class FooClass {
  var f: int
  var c: NestedModule.C
 
  constructor ()
}

datatype Friends = Agnes | Agatha | Jermaine

function SomeFunc(funcFormal: int, foo: FooClass): nat 
  reads foo, foo.c 
  ensures SomeFunc(funcFormal, foo) == foo.c.f
{ 
  3
}

method SomeMethod(methodFormal: int) returns (result: bool)
  requires methodFormal == 2
  ensures result == (methodFormal == 2) 
  // ensures forall x :: x == methodFormal
{
  m();
  var lambdaExpr := x => x + 1;
  var c := new FooClass();
  result := methodFormal == SomeFunc(42, c);
}

datatype ImapSimulator_<!A, B> = ImapSimulator(
  input: iset<A>,
  apply: A --> B)
{
  ghost predicate Valid() {
    forall i <- input :: apply.requires(i)
  }
}

type ImapSimulator<!A, B> =
  X: ImapSimulator_<A, B> |
  X.Valid() witness ImapSimulator(iset{}, (x: A) requires false => match() {})
";

    public ProverLogStabilityTest(ITestOutputHelper testOutputHelper) {
      this.testOutputHelper = testOutputHelper;
    }

    private static bool updateProverLog = false; // Should always be false in committed code

    /// <summary>
    /// This test is meant to detect _any_ changes in Dafny's verification behavior.
    /// Dafny's verification is powered by an SMT solver. For difficult inputs, such solvers may change their behavior,
    /// both in performance and outcome, even when tiny non-semantic changes such as changes in variable names,
    /// are made in the input.
    ///
    /// To detect whether it is possible that the verification of Dafny proofs has changed,
    /// this test compares the input Dafny sends to the SMT solver against what it was sending previously.
    ///
    /// If this test fails, that means a change was made to Dafny that changes the SMT input it sends.
    /// If this was intentional, you should update this test's expect file with the new SMT input.
    /// To do so, set the static field above "updateProverLog" to true, run this test, set the flag back to false, and
    /// run the test again to verify it works.
    /// The git history of updates to this test allows us to easily see when Dafny's verification has changed.
    ///
    /// If you make a change to Dafny verification and this test does not fail, then likely the Dafny code in the test
    /// does not sufficiently cover the language to detect your change. In that case, please update the test so it does.
    /// 
    /// Note that this test does not detect changes in DafnyPrelude.bpl
    /// 
    /// </summary>
    [Fact]
    public async Task ProverLogRegression() {
      var options = DafnyOptions.CreateUsingOldParser(new WriterFromOutputHelper(testOutputHelper));

      var filePath = Path.Combine(Directory.GetCurrentDirectory(), "expectedProverLog.smt2");
      var expectation = await File.ReadAllTextAsync(filePath);
      expectation = expectation.Replace("\r", "");
      var regularProverLog = await GetProverLogForProgramAsync(options, await GetBoogie(options, originalProgram));
      regularProverLog = regularProverLog.Replace("\r", "");
      if (updateProverLog) {
        var path = Path.GetFullPath(filePath).Replace("bin" + Path.DirectorySeparatorChar + "Debug" + Path.DirectorySeparatorChar + "net8.0" + Path.DirectorySeparatorChar, "");
        await File.WriteAllTextAsync(path, regularProverLog);
        await Console.Out.WriteLineAsync("Updated prover log file at " + path);
      } else {
        Assert.Equal(expectation, regularProverLog);
      }
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
      options.ProcessSolverOptions(new ErrorReporterSink(options), Microsoft.Dafny.Token.NoToken);
      using (var engine = ExecutionEngine.CreateWithoutSharedCache(options)) {
        foreach (var boogieProgram in boogiePrograms) {
          var (outcome, _) = await DafnyMain.BoogieOnce(new ErrorReporterSink(options),
            options, new StringWriter(), engine, "", "", boogieProgram, "programId");
        }
      }
      foreach (var proverFile in Directory.GetFiles(directory)) {
        yield return await File.ReadAllTextAsync(proverFile);
      }
      Directory.Delete(directory, true);
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
