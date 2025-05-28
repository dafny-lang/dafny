// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

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
  public class Modifications {
    private readonly DafnyOptions options;
    internal HashSet<int> preprocessedPrograms = [];
    // List of all types for which a {:synthesize} - annotated method is needed
    // These methods are used to get fresh instances of the corresponding types
    internal readonly List<UserDefinedType> TypesToSynthesize = [];
    public Modifications(DafnyOptions options) {
      this.options = options;
    }

    private readonly Dictionary<string, ProgramModification> idToModification = new();
    public ProgramModification GetProgramModification(Program program,
      Implementation impl, HashSet<string> capturedStates, HashSet<string> testEntryNames,
      string uniqueId) {
      if (!idToModification.ContainsKey(uniqueId)) {
        idToModification[uniqueId] =
          new ProgramModification(options, program, impl, capturedStates, testEntryNames, uniqueId);
      }
      return idToModification[uniqueId];
    }

    public IEnumerable<ProgramModification> Values => idToModification.Values;

    public int NumberOfBlocksCovered(HashSet<string> blockIds, bool onlyIfTestsExists = false) {
      var relevantModifications = Values.Where(modification =>
        modification.CounterexampleStatus == ProgramModification.Status.Success && (!onlyIfTestsExists || (modification.TestMethod != null && modification.TestMethod.IsValid)));
      return blockIds.Count(blockId =>
        relevantModifications.Any(mod => mod.CapturedStates.Contains(blockId)));
    }
  }

  /// <summary>
  /// Records a modification of the boogie program under test. The modified
  /// program has an assertion that should fail provided a certain block is
  /// visited / path is taken.
  /// </summary>
  public class ProgramModification {
    private DafnyOptions Options { get; }

    internal enum Status { Success, Failure, Untested }

    internal Status CounterexampleStatus;
    public readonly Implementation Implementation; // implementation under test

    internal readonly string uniqueId;
    public readonly HashSet<string> CapturedStates;

    private readonly HashSet<string> testEntryNames;
    private Program/*?*/ program;
    private string/*?*/ counterexampleLog;
    internal TestMethod TestMethod;

    public ProgramModification(DafnyOptions options, Program program, Implementation impl,
      HashSet<string> capturedStates,
      HashSet<string> testEntryNames, string uniqueId) {
      Options = options;
      Implementation = impl;
      CounterexampleStatus = Status.Untested;
      this.program = program;
      this.testEntryNames = testEntryNames;
      CapturedStates = capturedStates;
      this.uniqueId = uniqueId;
      counterexampleLog = null;
      TestMethod = null;
    }

    /// <summary>
    /// Setup DafnyOptions to prepare for counterexample extraction
    /// </summary>
    private static void SetupForCounterexamples(DafnyOptions options) {
      options.NormalizeNames = false;
      options.EmitDebugInformation = true;
      options.ErrorTrace = 1;
      options.EnhancedErrorMessages = 1;
      options.ModelViewFile = "-";
      options.Prune = options.TestGenOptions.ForcePrune;
      options.PruneInfeasibleEdges = false;  // because same implementation object is reused to generate multiple tests
    }

    /// <summary>
    /// Return the counterexample log produced by trying to verify this modified
    /// version of the original boogie program. Return null if this
    /// counterexample does not cover any new SourceModifications.
    /// </summary>
    public async Task<string>/*?*/ GetCounterExampleLog(Modifications cache) {
      if (CounterexampleStatus != Status.Untested ||
          (CapturedStates.Count != 0 && IsCovered(cache))) {
        return counterexampleLog;
      }
      var options = CopyForProcedure(Options, testEntryNames);
      SetupForCounterexamples(options);
      var writer = new StringWriter();
      if (!cache.preprocessedPrograms.Add(program.UniqueId)) {
        options.UseAbstractInterpretation = false; // running abs. inter. twice on the same program leads to errors
      }

      using (var engine = ExecutionEngine.CreateWithoutSharedCache(options)) {
        var guid = Guid.NewGuid().ToString();
        var result = await Task.WhenAny(engine.InferAndVerify(writer, program,
            new PipelineStatistics(), null,
            _ => { }, guid),
          Task.Delay(TimeSpan.FromSeconds(Options.TimeLimit <= 0
            ? TestGenerationOptions.DefaultTimeLimit
            : Options.TimeLimit)));
        program = null; // allows to garbage collect what is no longer needed
        CounterexampleStatus = Status.Failure;
        counterexampleLog = null;
        if (result is not Task<PipelineOutcome>) {
          if (Options.Verbose) {
            await options.OutputWriter.Status(
              $"// No test can be generated for {uniqueId} " +
              "because the verifier timed out.");
          }

          return counterexampleLog;
        }
      }

      var log = writer.ToString();
      // If Dafny finds several assertion violations (e.g. because of inlining one trap assertion multiple times),
      // pick the first execution trace and extract the counterexample from it
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
          CounterexampleStatus = Status.Success;
          var blockId = Regex.Replace(line, @"\s+", "").Split('|')[2];
          if (Options.Verbose &&
              Options.TestGenOptions.Mode != TestGenerationOptions.Modes.Path && !CapturedStates.Contains(blockId)) {
            await options.OutputWriter.Status($"// Test {uniqueId} covers {blockId}");
          }
          CapturedStates.Add(blockId);
        }
      }
      if (Options.Verbose && counterexampleLog == null) {
        if (log == "") {
          await options.OutputWriter.Status(
            $"// No test is generated for {uniqueId} " +
            "because the verifier proved that no inputs could cause this location to be visited.");
        } else if (log.Contains("MODEL") || log.Contains("anon0")) {
          await options.OutputWriter.Status(
            $"// No test is generated for {uniqueId} " +
            "because there is no enhanced error trace. This can be caused " +
            "by a bug in Boogie error reporting.");
        } else {
          await options.OutputWriter.Status(
            $"// No test is generated for {uniqueId} " +
            "because the verifier timed out.");
        }
      }
      return counterexampleLog;
    }

    /// <summary>
    /// Return a copy of the given DafnyOption instance that (for the purposes
    /// of test generation) is identical to the <param name="options"></param>
    /// parameter in everything except the value of the ProcsToCheck field that
    /// determines the procedures to be verified and should be set to the value of
    /// the <param name="proceduresToVerify"></param> parameter.
    /// </summary>
    internal static DafnyOptions CopyForProcedure(DafnyOptions options, HashSet<string> proceduresToVerify) {
      var copy = new DafnyOptions(options);
      copy.ProcsToCheck = proceduresToVerify.ToList();
      return copy;
    }

    public async Task<TestMethod> GetTestMethod(Modifications cache, DafnyInfo dafnyInfo, bool returnNullIfNotUnique = true) {
      if (Options.Verbose) {
        await dafnyInfo.Options.OutputWriter.Status(
          $"// Constructing the test for {uniqueId}...");
      }
      var log = await GetCounterExampleLog(cache);
      if (log == null) {
        return null;
      }
      TestMethod = new TestMethod(dafnyInfo, log, cache);
      if (!TestMethod.IsValid || !returnNullIfNotUnique) {
        return TestMethod;
      }
      var duplicate = cache.Values
        .Where(mod => mod != this && Equals(mod.TestMethod, TestMethod))
        .FirstOrDefault((ProgramModification)null);
      if (duplicate == null) {
        return TestMethod;
      }
      if (Options.Verbose) {
        await dafnyInfo.Options.OutputWriter.Status(
          $"// Test for {uniqueId} matches a test previously generated " +
          $"for {duplicate.uniqueId} - this may occur if the code under test is non-deterministic, " +
          $"if a method/function is not inlined, or the input parameters are of a type not supported by " +
          $"test generation (trait types and function types).");
      }
      return null;
    }

    public bool IsCovered(Modifications cache) => cache.NumberOfBlocksCovered(CapturedStates) == CapturedStates.Count;

  }
}
