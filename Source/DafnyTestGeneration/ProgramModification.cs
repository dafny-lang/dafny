#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using Microsoft.Dafny;
using Program = Microsoft.Boogie.Program;

namespace DafnyTestGeneration {
  public class Modifications {
    private readonly DafnyOptions options;
    public Modifications(DafnyOptions options) {
      this.options = options;
    }

    private readonly Dictionary<string, ProgramModification> idToModification = new();
    public ProgramModification GetProgramModification(Program program,
      Implementation impl, HashSet<string> capturedStates, string procedure,
      string uniqueId) {
      if (!idToModification.ContainsKey(uniqueId)) {
        idToModification[uniqueId] =
          new ProgramModification(options, program, impl, capturedStates, procedure, uniqueId);
      }
      return idToModification[uniqueId];
    }

    public IEnumerable<ProgramModification> Values => idToModification.Values;

    public int NumberOfBlocksCovered(Implementation implementation, bool onlyIfTestsExists = false) {
      return NumberOfBlocksCovered(implementation.Blocks
        .Where(block => Utils.GetBlockId(block) != block.Label)
        .Select(Utils.GetBlockId).ToHashSet(), onlyIfTestsExists);
    }

    public int NumberOfBlocksCovered(HashSet<string> blockIds, bool onlyIfTestsExists = false) {
      var relevantModifications = Values.Where(modification =>
        modification.counterexampleStatus == ProgramModification.Status.Success && (!onlyIfTestsExists || (modification.testMethod != null && modification.testMethod.IsValid)));
      return blockIds.Count(blockId =>
        relevantModifications.Any(mod => mod.CapturedStates.Contains(blockId)));
    }

    internal int ModificationsWithStatus(Implementation implementation, ProgramModification.Status status) =>
      Values.Where(modification =>
          modification.implementation == implementation)
        .Count(mod => mod.counterexampleStatus == status);
  }

  /// <summary>
  /// Records a modification of the boogie program under test. The modified
  /// program has an assertion that should fail provided a certain block is
  /// visited / path is taken.
  /// </summary>
  public class ProgramModification {
    public DafnyOptions Options { get; }

    internal enum Status { Success, Failure, Untested }

    internal Status counterexampleStatus;
    public readonly Implementation implementation; // implementation under test

    private readonly string uniqueId;
    public readonly HashSet<string> CapturedStates;

    private readonly string procedure; // procedure to start verification from
    private Program/*?*/ program;
    private string/*?*/ counterexampleLog;
    internal TestMethod testMethod;

    public ProgramModification(DafnyOptions options, Program program, Implementation impl,
      HashSet<string> capturedStates,
      string procedure, string uniqueId) {
      Options = options;
      implementation = impl;
      counterexampleStatus = Status.Untested;
      this.program = Utils.DeepCloneProgram(options, program);
      this.procedure = procedure;
      CapturedStates = capturedStates;
      this.uniqueId = uniqueId;
      counterexampleLog = null;
      testMethod = null;
    }

    /// <summary>
    /// Setup DafnyOptions to prepare for counterexample extraction
    /// </summary>
    private static void SetupForCounterexamples(DafnyOptions options) {
      // Figure out the Z3 version in use:
      var proverOptions = new SMTLibSolverOptions(options);
      proverOptions.Parse(options.ProverOptions);
      var z3Version = DafnyOptions.GetZ3Version(proverOptions.ProverPath);
      // Based on Z3 version, determine the options to use:
      var optionsToAdd = new List<string>() {
        "O:model_evaluator.completion=true",
        "O:model.completion=true"
      };
      if (z3Version is null || z3Version < new Version(4, 8, 6)) {
        optionsToAdd.Add("O:model_compress=false");
      } else {
        optionsToAdd.Add("O:model.compact=false");
      }
      // (Re)set the options necessary for counterexample extraction:
      foreach (var option in optionsToAdd) {
        options.ProverOptions.RemoveAll(o => o.Split("=") == option.Split("="));
        options.ProverOptions.Add(option);
      }
      options.NormalizeNames = false;
      options.EmitDebugInformation = true;
      options.ErrorTrace = 1;
      options.EnhancedErrorMessages = 1;
      options.ModelViewFile = "-";
      options.Prune = !options.TestGenOptions.DisablePrune;
    }

    /// <summary>
    /// Return the counterexample log produced by trying to verify this modified
    /// version of the original boogie program. Return null if this
    /// counterexample does not cover any new SourceModifications.
    /// </summary>
    public async Task<string>/*?*/ GetCounterExampleLog(Modifications cache) {
      if (counterexampleStatus != Status.Untested ||
          (CapturedStates.Count != 0 && IsCovered(cache))) {
        return counterexampleLog;
      }
      var options = GenerateTestsCommand.CopyForProcedure(Options, procedure);
      SetupForCounterexamples(options);
      var engine = ExecutionEngine.CreateWithoutSharedCache(options);
      var guid = Guid.NewGuid().ToString();
      program.Resolve(options);
      program.Typecheck(options);
      // TODO: Remove next 3 lines when latest changes with Boogie are merged
      /*engine.EliminateDeadVariables(program);
      engine.CollectModSets(program);
      engine.Inline(program);*/
      var writer = new StringWriter();
      var result = await Task.WhenAny(engine.InferAndVerify(writer, program,
            new PipelineStatistics(), null,
            _ => { }, guid),
          Task.Delay(TimeSpan.FromSeconds(Options.TimeLimit <= 0 ?
            TestGenerationOptions.DefaultTimeLimit : Options.TimeLimit)));
      program = null; // allows to garbage collect what is no longer needed
      counterexampleStatus = Status.Failure;
      counterexampleLog = null;
      if (result is not Task<PipelineOutcome>) {
        if (Options.Verbose) {
          await options.OutputWriter.WriteLineAsync(
            $"// No test can be generated for {uniqueId} " +
            "because the verifier timed out.");
        }
        return counterexampleLog;
      }
      var log = writer.ToString();
      const string executionTraceString = "Execution trace";
      var firstTraceIndex = log.IndexOf(executionTraceString, 0, StringComparison.Ordinal);
      if (firstTraceIndex > 0 && log.Length > firstTraceIndex + executionTraceString.Length) {
        var secondTraceIndex = log.IndexOf(executionTraceString, firstTraceIndex + executionTraceString.Length, StringComparison.Ordinal);
        if (secondTraceIndex > 0) {
          log = log[..secondTraceIndex];
        }
      }
      // make sure that there is a counterexample (i.e. no parse errors, etc):
      var stringReader = new StringReader(log);
      while (await stringReader.ReadLineAsync() is { } line) {
        if (line.StartsWith("Block |")) {
          counterexampleLog = log;
          counterexampleStatus = Status.Success;
          var blockId = Regex.Replace(line, @"\s+", "").Split('|')[2];
          if (Options.Verbose &&
              Options.TestGenOptions.Mode != TestGenerationOptions.Modes.Path && !CapturedStates.Contains(blockId)) {
            await options.OutputWriter.WriteLineAsync($"// Test {uniqueId} covers {blockId}");
          }
          CapturedStates.Add(blockId);
        }
      }
      if (Options.Verbose && counterexampleLog == null) {
        if (log == "") {
          await options.OutputWriter.WriteLineAsync(
            $"// No test is generated for {uniqueId} " +
            "because the verifier proved that no inputs could cause this location to be visited.");
        } else if (log.Contains("MODEL") || log.Contains("anon0")) {
          await options.OutputWriter.WriteLineAsync(
            $"// No test is generated for {uniqueId} " +
            "because there is no enhanced error trace. This can be caused " +
            "by a bug in boogie counterexample model parsing.");
        } else {
          await options.OutputWriter.WriteLineAsync(
            $"// No test is generated for {uniqueId} " +
            "because the verifier timed out.");
        }
      }
      return counterexampleLog;
    }

    public async Task<TestMethod> GetTestMethod(Modifications cache, DafnyInfo dafnyInfo, bool returnNullIfNotUnique = true) {
      if (Options.Verbose) {
        await dafnyInfo.Options.OutputWriter.WriteLineAsync(
          $"// Extracting the test for {uniqueId} from the counterexample...");
      }
      var log = await GetCounterExampleLog(cache);
      if (log == null) {
        return null;
      }
      testMethod = new TestMethod(dafnyInfo, log);
      if (!testMethod.IsValid || !returnNullIfNotUnique) {
        return testMethod;
      }
      var duplicate = cache.Values
        .Where(mod => mod != this && Equals(mod.testMethod, testMethod))
        .FirstOrDefault((ProgramModification)null);
      if (duplicate == null) {
        return testMethod;
      }
      if (Options.Verbose) {
        await dafnyInfo.Options.OutputWriter.WriteLineAsync(
          $"// Test for {uniqueId} matches a test previously generated " +
          $"for {duplicate.uniqueId} - skipping.");
      }
      // return testMethod;
      return null;
    }
    
    public bool IsCovered(Modifications cache) => cache.NumberOfBlocksCovered(CapturedStates) == CapturedStates.Count;
    
  }
}
