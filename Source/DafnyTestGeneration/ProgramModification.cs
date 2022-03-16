using System;
using System.Collections.Generic;
using System.IO;
using System.Text.RegularExpressions;
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

    public ProgramModification(Program program, string procedure) {
      this.program = DeepCloneProgram(program);
      this.procedure = procedure;
    }

    /// <summary>
    /// Deep clone the program.
    /// </summary>
    private static Program DeepCloneProgram(Program program) {
      var oldPrintInstrumented = DafnyOptions.O.PrintInstrumented;
      var oldPrintFile = DafnyOptions.O.PrintFile;
      DafnyOptions.O.PrintInstrumented = true;
      DafnyOptions.O.PrintFile = "-";
      var textRepresentation = Utils.CaptureConsoleOutput(
        () => program.Emit(new TokenTextWriter(Console.Out, DafnyOptions.O)));
      Microsoft.Boogie.Parser.Parse(textRepresentation, "", out var copy);
      DafnyOptions.O.PrintInstrumented = oldPrintInstrumented;
      DafnyOptions.O.PrintFile = oldPrintFile;
      return copy;
    }

    /// <summary>
    /// Setup CommandLineArguments to prepare verification. This is necessary
    /// because the procsToCheck field in CommandLineOptions (part of Boogie)
    /// is private meaning that the only way of setting this field is by calling
    /// options.Parse() on a new DafnyObject.
    /// </summary>
    private static DafnyOptions SetupOptions(string procedure) {
      var options = new DafnyOptions();
      options.Parse(new[] { "/proc:" + procedure });
      options.NormalizeNames = false;
      options.EmitDebugInformation = true;
      options.EnhancedErrorMessages = 1;
      options.ModelViewFile = "-";
      options.ProverOptions = new List<string>() {
        "O:model_compress=false",
        "O:model_evaluator.completion=true",
        "O:model.completion=true"
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
    public virtual string? GetCounterExampleLog() {
      var oldOptions = DafnyOptions.O;
      var options = SetupOptions(procedure);
      DafnyOptions.Install(options);
      var engine = ExecutionEngine.CreateWithoutSharedCache(options);
      var uniqueId = Guid.NewGuid().ToString();
      program.Resolve(options);
      program.Typecheck(options);
      engine.EliminateDeadVariables(program);
      engine.CollectModSets(program);
      engine.CoalesceBlocks(program);
      engine.Inline(program);
      var log = Utils.CaptureConsoleOutput(
        () => engine.InferAndVerify(program,
          new PipelineStatistics(), null,
          _ => { }, uniqueId));
      DafnyOptions.Install(oldOptions);
      // make sure that there is a counterexample (i.e. no parse errors, etc):
      string? line;
      var stringReader = new StringReader(log);
      while ((line = stringReader.ReadLine()) != null) {
        if (line.StartsWith("Block |")) {
          return log;
        }
      }
      return null;
    }
  }
}