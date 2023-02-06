#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Program = Microsoft.Boogie.Program;

namespace DafnyTestGeneration {

  /// <summary>
  /// Records a modification of the boogie program under test. The modified
  /// program has an assertion that should fail provided a certain block is
  /// visited / path is taken.
  /// </summary>
  public class ProgramModification {

    private static Dictionary<string, ProgramModification>
      idToModification = new();

    private enum Status { Success, Failure, Untested }

    private Status counterexampleStatus;
    private readonly Implementation implementation; // implementation under test

    private readonly string uniqueId;
    public readonly HashSet<string> CapturedStates;

    private readonly string procedure; // procedure to start verification from
    private Program/*?*/ program;
    private readonly HashSet<int> coversBlocks;
    private string/*?*/ counterexampleLog;
    private TestMethod testMethod;

    public static ProgramModification GetProgramModification(Program program,
      Implementation impl, HashSet<int> coversBlocks, HashSet<string> capturedStates, string procedure,
      string uniqueId) {
      if (!idToModification.ContainsKey(uniqueId)) {
        idToModification[uniqueId] =
          new ProgramModification(program, impl, coversBlocks, capturedStates, procedure,
            uniqueId);
      }
      return idToModification[uniqueId];
    }

    private ProgramModification(Program program, Implementation impl,
      HashSet<int> coversBlocks, HashSet<string> capturedStates,
      string procedure, string uniqueId) {
      implementation = impl;
      counterexampleStatus = Status.Untested;
      this.program = Utils.DeepCloneProgram(program);
      this.procedure = procedure;
      this.coversBlocks = coversBlocks;
      CapturedStates = capturedStates;
      this.uniqueId = uniqueId;
      counterexampleLog = null;
      testMethod = null;
    }

    /// <summary>
    /// Setup CommandLineArguments to prepare verification. This is necessary
    /// because the procsToCheck field in CommandLineOptions (part of Boogie)
    /// is private meaning that the only way of setting this field is by calling
    /// options.Parse() on a new DafnyObject.
    /// </summary>
    private static DafnyOptions SetupOptions(string procedure) {
      var options = DafnyOptions.Create();
      options.Parse(new[] { "/proc:" + procedure });
      options.NormalizeNames = false;
      options.EmitDebugInformation = true;
      options.ErrorTrace = 1;
      options.EnhancedErrorMessages = 1;
      options.ModelViewFile = "-";
      options.ProverOptions = new List<string>() {
        // TODO: condition this on Z3 version
        "O:model.compact=false",
        "O:model_evaluator.completion=true",
        "O:model.completion=true"
      };
      options.Prune = !DafnyOptions.O.TestGenOptions.DisablePrune;
      options.ProverOptions.AddRange(DafnyOptions.O.ProverOptions);
      options.LoopUnrollCount = DafnyOptions.O.LoopUnrollCount;
      options.DefiniteAssignmentLevel = DafnyOptions.O.DefiniteAssignmentLevel;
      options.WarnShadowing = DafnyOptions.O.WarnShadowing;
      options.VerifyAllModules = DafnyOptions.O.VerifyAllModules;
      options.TimeLimit = DafnyOptions.O.TimeLimit;
      return options;
    }

    /// <summary>
    /// Return the counterexample log produced by trying to verify this modified
    /// version of the original boogie program. Return null if this
    /// counterexample does not cover any new SourceModifications.
    /// </summary>
    public async Task<string>/*?*/ GetCounterExampleLog() {
      if (counterexampleStatus != Status.Untested ||
          (coversBlocks.Count != 0 && IsCovered)) {
        return counterexampleLog;
      }
      var oldOptions = DafnyOptions.O;
      var options = SetupOptions(procedure);
      DafnyOptions.Install(options);
      var engine = ExecutionEngine.CreateWithoutSharedCache(options);
      var guid = Guid.NewGuid().ToString();
      program.Resolve(options);
      program.Typecheck(options);
      engine.EliminateDeadVariables(program);
      engine.CollectModSets(program);
      engine.Inline(program);
      var writer = new StringWriter();
      var result = await Task.WhenAny(engine.InferAndVerify(writer, program,
            new PipelineStatistics(), null,
            _ => { }, guid),
          Task.Delay(TimeSpan.FromSeconds(oldOptions.TimeLimit <= 0 ?
            TestGenerationOptions.DefaultTimeLimit : oldOptions.TimeLimit)));
      program = null; // allows to garbage collect what is no longer needed
      counterexampleStatus = Status.Failure;
      counterexampleLog = null;
      DafnyOptions.Install(oldOptions);
      if (result is not Task<PipelineOutcome>) {
        if (DafnyOptions.O.TestGenOptions.Verbose) {
          Console.WriteLine(
            $"// No test can be generated for {uniqueId} " +
            "because the verifier timed out.");
        }
        return counterexampleLog;
      }
      var log = writer.ToString();
      // make sure that there is a counterexample (i.e. no parse errors, etc):
      var stringReader = new StringReader(log);
      while (await stringReader.ReadLineAsync() is { } line) {
        if (line.StartsWith("Block |")) {
          counterexampleLog = log;
          counterexampleStatus = Status.Success;
          var blockId = int.Parse(Regex.Replace(line, @"\s+", "").Split('|')[2]);
          coversBlocks.Add(blockId);
          if (DafnyOptions.O.TestGenOptions.Verbose) {
            Console.WriteLine($"// Test {uniqueId} covers block {blockId}");
          }
        }
      }
      if (DafnyOptions.O.TestGenOptions.Verbose && counterexampleLog == null) {
        if (log == "") {
          Console.WriteLine(
            $"// No test can be generated for {uniqueId} " +
            "because the verifier suceeded.");
        } else if (log.Contains("MODEL")) {
          Console.WriteLine(
            $"// No test can be generated for {uniqueId} " +
            "because there is no enhanced error trace.");
        } else if (log.Contains("anon0")) {
          Console.WriteLine(
            $"// No test can be generated for {uniqueId} " +
            "because the model cannot be extracted.");
        } else {
          Console.WriteLine(
            $"// No test can be generated for {uniqueId} " +
            "because the verifier timed out.");
        }
      }
      return counterexampleLog;
    }

    public async Task<TestMethod> GetTestMethod(DafnyInfo dafnyInfo, bool returnNullIfNotUnique = true) {
      if (DafnyOptions.O.TestGenOptions.Verbose) {
        Console.WriteLine(
          $"// Extracting the test for {uniqueId} from the counterexample...");
      }
      var log = await GetCounterExampleLog();
      if (log == null) {
        return null;
      }
      testMethod = new TestMethod(dafnyInfo, log);
      if (!testMethod.IsValid || !returnNullIfNotUnique) {
        return testMethod;
      }
      var duplicate = ModificationsForImplementation(implementation)
        .Where(mod => mod != this && Equals(mod.testMethod, testMethod))
        .FirstOrDefault((ProgramModification)null);
      if (duplicate == null) {
        return testMethod;
      }
      if (DafnyOptions.O.TestGenOptions.Verbose) {
        Console.WriteLine(
          $"// Test for {uniqueId} matches a test previously generated " +
          $"for {duplicate.uniqueId}.");
      }
      return null;
    }

    private static IEnumerable<ProgramModification>
      ModificationsForImplementation(Implementation implementation) =>
      idToModification.Values.Where(modification =>
        modification.implementation == implementation ||
        DafnyOptions.O.TestGenOptions.TargetMethod != null);

    private static bool BlocksAreCovered(Implementation implementation, HashSet<int> blockIds, bool onlyIfTestsExists = false) {
      var relevantModifications = ModificationsForImplementation(implementation).Where(modification =>
        modification.counterexampleStatus == Status.Success && (!onlyIfTestsExists || (modification.testMethod != null && modification.testMethod.IsValid)));
      return blockIds.All(blockId =>
        relevantModifications.Any(mod => mod.coversBlocks.Contains(blockId)));
    }
    public bool IsCovered => BlocksAreCovered(implementation, coversBlocks);

    public static void ResetStatistics() {
      idToModification = new();
    }
  }
}
