using System;
using System.Collections.Generic;
using System.IO;
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

    private readonly string procedure; // procedure to be tested
    private readonly Program program;
    public readonly string uniqueId;
    private static int id;

    public ProgramModification(Program program, string procedure, string uniqueId) {
      id++;
      this.program = Utils.DeepCloneProgram(program);
      this.procedure = procedure;
      this.uniqueId = uniqueId;
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
      options.Prune = true;
      options.ProverOptions = new List<string>() {
        "O:model_compress=false",
        "O:model_evaluator.completion=true"
      };
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
    public virtual async Task<string?> GetCounterExampleLog() {
      var oldOptions = DafnyOptions.O;
      var options = SetupOptions(procedure);
      DafnyOptions.Install(options);
      var engine = ExecutionEngine.CreateWithoutSharedCache(options);
      var guid = Guid.NewGuid().ToString();
      program.Resolve(options);
      program.Typecheck(options);
      engine.EliminateDeadVariables(program);
      engine.CollectModSets(program);
      engine.CoalesceBlocks(program);
      engine.Inline(program);
      var writer = new StringWriter();
      await Task.WhenAny(engine.InferAndVerify(writer, program,
        new PipelineStatistics(), null,
        _ => { }, guid), 
        Task.Delay(TimeSpan.FromSeconds(oldOptions.TestGenOptions.Timeout)));
      var log = writer.ToString();
      DafnyOptions.Install(oldOptions);
      // make sure that there is a counterexample (i.e. no parse errors, etc):
      var stringReader = new StringReader(log);
      while (await stringReader.ReadLineAsync() is { } line) {
        if (line.StartsWith("Block |")) {
          return log;
        }
      }
      if (DafnyOptions.O.TestGenOptions.Verbose) {
        Console.WriteLine(
          $"// No test can be generated for {uniqueId} because the verifier timed out or gave no counterexample (can happen if the block has dead code).");
      }
      return null;
    }
  }
}