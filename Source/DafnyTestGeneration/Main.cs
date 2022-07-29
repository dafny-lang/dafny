using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;

namespace DafnyTestGeneration {

  public static class Main {

    /// <summary>
    /// This method returns each capturedState that is unreachable, one by one,
    /// and then a line with the summary of how many such states there are, etc.
    /// Note that loop unrolling may cause false positives and the absence of
    /// loop unrolling may cause false negatives.
    /// </summary>
    /// <returns></returns>
    public static async IAsyncEnumerable<string> GetDeadCodeStatistics(Program program) {
      
      ProgramModification.ResetStatistics();
      var modifications = GetModifications(program).ToEnumerable().ToList();
      var blocksReached = modifications.Count;
      HashSet<string> allStates = new();
      HashSet<string> allDeadStates = new();

      // Generate tests based on counterexamples produced from modifications
      for (var i = modifications.Count - 1; i >= 0; i--) {
        await modifications[i].GetCounterExampleLog();
        var deadStates = new HashSet<string>();
        if (!modifications[i].IsCovered) {
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

    public static async IAsyncEnumerable<string> GetDeadCodeStatistics(string sourceFile) {
      var source = await new StreamReader(sourceFile).ReadToEndAsync();
      var program = Utils.Parse(source, sourceFile);
      if (program == null) {
        yield return "Cannot parse program";
        yield break;
      }
      await foreach (var line in GetDeadCodeStatistics(program)) {
        yield return line;
      }
    }

    private static IAsyncEnumerable<ProgramModification> GetModifications(Program program) {
      var dafnyInfo = new DafnyInfo(program);
      // Translate the Program to Boogie:
      var oldPrintInstrumented = DafnyOptions.O.PrintInstrumented;
      DafnyOptions.O.PrintInstrumented = true;
      var boogiePrograms = Translator
        .Translate(program, program.Reporter)
        .ToList().ConvertAll(tuple => tuple.Item2);
      DafnyOptions.O.PrintInstrumented = oldPrintInstrumented;

      // Create modifications of the program with assertions for each block\path
      ProgramModifier programModifier =
        DafnyOptions.O.TestGenOptions.Mode == TestGenerationOptions.Modes.Path
          ? new PathBasedModifier()
          : new BlockBasedModifier();
      return programModifier.GetModifications(boogiePrograms, dafnyInfo);
    }

    /// <summary>
    /// Generate test methods for a certain Dafny program.
    /// </summary>
    /// <returns></returns>
    public static async IAsyncEnumerable<TestMethod> GetTestMethodsForProgram(Program program) {
      
      ProgramModification.ResetStatistics();
      var dafnyInfo = new DafnyInfo(program);
      HashSet<Implementation> implementations = new();
      Dictionary<Implementation, int> testCount = new();
      Dictionary<Implementation, int> failedTestCount = new();
      // Generate tests based on counterexamples produced from modifications
      await foreach (var modification in GetModifications(program)) {
        var log = await modification.GetCounterExampleLog();
        implementations.Add(modification.Implementation);
        if (log == null) {
          continue;
        }
        var testMethod = await modification.GetTestMethod(dafnyInfo);
        if (testMethod == null) {
          continue;
        }
        if (!testMethod.IsValid) {
          failedTestCount[modification.Implementation] =
            failedTestCount.GetValueOrDefault(modification.Implementation, 0) +
            1;
        }
        testCount[modification.Implementation] =
          testCount.GetValueOrDefault(modification.Implementation, 0) + 1;
        yield return testMethod;
      }

      if (DafnyOptions.O.TestGenOptions.PrintTargets != null) {
        TargetPrinter printer = new TargetPrinter(dafnyInfo);
        printer.PopulateTargetedMethods(testCount, true);
        printer.PopulateTargetedMethods(failedTestCount, false);
        printer.WriteToFile(DafnyOptions.O.TestGenOptions.PrintTargets);
      }

      if (DafnyOptions.O.TestGenOptions.Verbose) {
        foreach (var implementation in implementations) {
          int blocks = implementation.Blocks.Count;
          int failedQueries = ProgramModification.ModificationsWithStatus(implementation,
            ProgramModification.Status.Failure);
          int queries = failedQueries +
                        ProgramModification.ModificationsWithStatus(implementation,
                          ProgramModification.Status.Success);
          int tests = testCount.GetValueOrDefault(implementation, 0);
          int failedTests = failedTestCount.GetValueOrDefault(implementation, 0);
          if (ProgramModification.ImplementationIsCovered(implementation)) {
            Console.WriteLine(
              $"// Procedure {implementation} ({blocks} " +
              $"blocks) is completely covered by " +
              $"{tests} (failed to extract {failedTests}) " +
              $"tests generated using {queries} SMT queries " +
              $"(failed {failedQueries} queries)");
          } else {
            Console.WriteLine(
              $"// Procedure {implementation} ({blocks} " +
              $"blocks) is not fully covered by " +
              $"{tests} (failed to extract {failedTests}) " +
              $"tests generated using {queries} SMT queries " +
              $"(failed {failedQueries} queries)");
          }
        }
      }
    }

    /// <summary>
    /// Return a Dafny class (list of lines) with tests for the given Dafny file
    /// </summary>
    public static async IAsyncEnumerable<string> GetTestClassForProgram(string sourceFile) {

      TestMethod.ClearTypesToSynthesize();
      var source = new StreamReader(sourceFile).ReadToEnd();
      var program = Utils.Parse(source, sourceFile);
      if (program == null) {
        yield break;
      }
      var dafnyInfo = new DafnyInfo(program);
      var rawName = Path.GetFileName(sourceFile).Split(".").First();

      string EscapeDafnyStringLiteral(string str) {
        return $"\"{str.Replace(@"\", @"\\")}\"";
      }

      yield return $"include {EscapeDafnyStringLiteral(sourceFile)}";
      yield return $"module {rawName}UnitTests {{";
      foreach (var module in dafnyInfo.ToImportAs.Keys) {
        // TODO: disambiguate between modules amongst generated tests
        if (module.Split(".").Last() == dafnyInfo.ToImportAs[module]) {
          yield return $"import {module}";
        } else {
          yield return $"import {dafnyInfo.ToImportAs[module]} = {module}";
        }
      }

      await foreach (var method in GetTestMethodsForProgram(program)) {
        yield return method.ToString();
      }

      yield return TestMethod.EmitSynthesizeMethods();

      yield return "}";
    }
  }
}