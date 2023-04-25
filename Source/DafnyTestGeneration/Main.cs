#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;

namespace DafnyTestGeneration {

  public static class Main {

    public static bool setNonZeroExitCode = false;

    /// <summary>
    /// This method returns each capturedState that is unreachable, one by one,
    /// and then a line with the summary of how many such states there are, etc.
    /// Note that loop unrolling may cause false positives and the absence of
    /// loop unrolling may cause false negatives.
    /// </summary>
    /// <returns></returns>
    public static async IAsyncEnumerable<string> GetDeadCodeStatistics(Program program) {

      program.Reporter.Options.PrintMode = PrintModes.Everything;

      var cache = new Modifications(program.Options);
      var modifications = GetModifications(cache, program).ToList();
      var blocksReached = modifications.Count;
      HashSet<string> allStates = new();
      HashSet<string> allDeadStates = new();

      // Generate tests based on counterexamples produced from modifications
      for (var i = modifications.Count - 1; i >= 0; i--) {
        await modifications[i].GetCounterExampleLog(cache);
        var deadStates = new HashSet<string>();
        if (!modifications[i].IsCovered(cache)) {
          deadStates = modifications[i].CapturedStates;
        }

        if (deadStates.Count != 0) {
          foreach (var capturedState in deadStates) {
            yield return $"Code at {capturedState} is potentially unreachable.";
          }
          blocksReached--;
          allDeadStates.UnionWith(deadStates);
        }
        allStates.UnionWith(modifications[i].CapturedStates);
      }

      yield return $"Out of {modifications.Count} basic blocks " +
                   $"({allStates.Count} capturedStates), {blocksReached} " +
                   $"({allStates.Count - allDeadStates.Count}) are reachable. " +
                   "There might be false negatives if you are not unrolling " +
                   "loops. False positives are always possible.";
    }

    public static async IAsyncEnumerable<string> GetDeadCodeStatistics(string sourceFile, DafnyOptions options) {
      options.PrintMode = PrintModes.Everything;
      var source = await new StreamReader(sourceFile).ReadToEndAsync();
      var program = Utils.Parse(options, source, sourceFile);
      if (program == null) {
        yield return "Cannot parse program";
        yield break;
      }
      await foreach (var line in GetDeadCodeStatistics(program)) {
        yield return line;
      }
    }

    private static IEnumerable<ProgramModification> GetModifications(Modifications cache, Program program) {
      var options = program.Options;
      var dafnyInfo = new DafnyInfo(program);
      setNonZeroExitCode = dafnyInfo.SetNonZeroExitCode || setNonZeroExitCode;
      // Translate the Program to Boogie:
      var oldPrintInstrumented = options.PrintInstrumented;
      options.PrintInstrumented = true;
      var boogiePrograms = Utils.Translate(program);
      options.PrintInstrumented = oldPrintInstrumented;

      if (options.TestGenOptions.TargetMethod != null) {
        var targetFound = boogiePrograms.Any(program =>
          program.Implementations.Any(i =>
            i.Name.StartsWith("Impl$$") &&
            i.VerboseName.Split(" ")[0]
            == options.TestGenOptions.TargetMethod));
        if (!targetFound) {
          options.Printer.ErrorWriteLine(Console.Error,
            "Error: Cannot find method " +
            options.TestGenOptions.TargetMethod +
            " (is this name fully-qualified?)");
          setNonZeroExitCode = true;
          return new List<ProgramModification>();
        }
      }

      // Create modifications of the program with assertions for each block\path
      ProgramModifier programModifier =
        options.TestGenOptions.Mode == TestGenerationOptions.Modes.Path
          ? new PathBasedModifier(cache)
          : new BlockBasedModifier(cache);
      return programModifier.GetModifications(boogiePrograms, dafnyInfo);
    }

    /// <summary>
    /// Generate test methods for a certain Dafny program.
    /// </summary>
    /// <returns></returns>
    public static async IAsyncEnumerable<TestMethod> GetTestMethodsForProgram(Program program, Modifications cache=null) {

      var options = program.Options;
      options.PrintMode = PrintModes.Everything;
      var dafnyInfo = new DafnyInfo(program);
      setNonZeroExitCode = dafnyInfo.SetNonZeroExitCode || setNonZeroExitCode;
      // Generate tests based on counterexamples produced from modifications

      cache ??= new Modifications(options);
      var programModifications = GetModifications(cache, program).ToList();
      foreach (var modification in programModifications) {

        var log = await modification.GetCounterExampleLog(cache);
        if (log == null) {
          continue;
        }
        var testMethod = await modification.GetTestMethod(cache, dafnyInfo);
        if (testMethod == null) {
          continue;
        }
        yield return testMethod;
      }
      setNonZeroExitCode = dafnyInfo.SetNonZeroExitCode || setNonZeroExitCode;
    }

    /// <summary>
    /// Return a Dafny class (list of lines) with tests for the given Dafny file
    /// </summary>
    public static async IAsyncEnumerable<string> GetTestClassForProgram(string sourceFile, DafnyOptions options) {

      options.PrintMode = PrintModes.Everything;
      TestMethod.ClearTypesToSynthesize();
      var source = await new StreamReader(sourceFile).ReadToEndAsync();
      var program = Utils.Parse(options, source, sourceFile);
      if (program == null) {
        yield break;
      }
      if (Utils.AttributeFinder.ProgramHasAttribute(program,
            TestGenerationOptions.TestInlineAttribute)) {
        options.VerifyAllModules = true;
        program = Utils.Parse(options, source, sourceFile);
        if (program == null) {
          yield break;
        }
      }
      var dafnyInfo = new DafnyInfo(program);
      setNonZeroExitCode = dafnyInfo.SetNonZeroExitCode || setNonZeroExitCode;
      var rawName = Regex.Replace(sourceFile, "[^a-zA-Z0-9_]", "");

      string EscapeDafnyStringLiteral(string str) {
        return $"\"{str.Replace(@"\", @"\\")}\"";
      }

      yield return $"include {EscapeDafnyStringLiteral(sourceFile)}";
      yield return $"module {rawName}UnitTests {{";
      foreach (var module in dafnyInfo.ToImportAs.Keys) {
        if (module.Split(".").Last() == dafnyInfo.ToImportAs[module]) {
          yield return $"import {module}";
        } else {
          yield return $"import {dafnyInfo.ToImportAs[module]} = {module}";
        }
      }
      
      var cache = new Modifications(options);
      var methodsGenerated = 0;
      await foreach (var method in GetTestMethodsForProgram(program, cache)) {
        yield return method.ToString();
        methodsGenerated++;
      }
      
      foreach (var implementation in cache.Values
                 .Select(modification => modification.implementation).ToHashSet()) {
        int failedQueries = cache.ModificationsWithStatus(implementation,
          ProgramModification.Status.Failure);
        int queries = failedQueries + cache.ModificationsWithStatus(implementation,
          ProgramModification.Status.Success);
        int blocks = implementation.Blocks.Count(block => block.Cmds.Count != 0);
        int coveredByCounterexamples = cache.NumberOfBlocksCovered(implementation);
        int coveredByTests = cache.NumberOfBlocksCovered(implementation, onlyIfTestsExists: true);
        yield return $"// Out of {blocks} non-empty blocks in the " +
                     $"{implementation.VerboseName.Split(" ")[0]} method, " +
                     $"{coveredByTests} should be covered by tests " +
                     $"(assuming no tests were found to be duplicates of each other). " +
                     $"Moreover, {coveredByCounterexamples} blocks have been found to be reachable " +
                     $"(i.e. the verifier returned a counterexample and did not timeout). " +
                     $"A total of {queries} SMT queries were made to cover " +
                     $"this method or the method into which this method was inlined. " +
                     $"{failedQueries} queries did not return a counterexample.";
      }

      yield return TestMethod.EmitSynthesizeMethods(dafnyInfo);
      yield return "}";

      if (methodsGenerated == 0) {
        options.Printer.ErrorWriteLine(Console.Error,
          "Error: No tests were generated, because no code points could be " +
          "proven reachable (do you have a false assumption in the program?)");
        setNonZeroExitCode = true;
      }
    }
  }
}
