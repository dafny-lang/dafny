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
      ProgramModification.ResetStatistics();
      var modifications = GetModifications(program).ToList();
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

    private static IEnumerable<ProgramModification> GetModifications(Program program) {
      var options = program.Options;
      var dafnyInfo = new DafnyInfo(program);
      setNonZeroExitCode = dafnyInfo.SetNonZeroExitCode || setNonZeroExitCode;
      // Translate the Program to Boogie:
      var oldPrintInstrumented = options.PrintInstrumented;
      options.PrintInstrumented = true;
      var boogiePrograms = Translator
        .Translate(program, program.Reporter)
        .ToList().ConvertAll(tuple => tuple.Item2);
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
          ? new PathBasedModifier()
          : new BlockBasedModifier();
      return programModifier.GetModifications(boogiePrograms, dafnyInfo);
    }

    /// <summary>
    /// Generate test methods for a certain Dafny program.
    /// </summary>
    /// <returns></returns>
    public static async IAsyncEnumerable<TestMethod> GetTestMethodsForProgram(Program program) {

      var options = program.Options;
      options.PrintMode = PrintModes.Everything;
      ProgramModification.ResetStatistics();
      var dafnyInfo = new DafnyInfo(program);
      setNonZeroExitCode = dafnyInfo.SetNonZeroExitCode || setNonZeroExitCode;
      // Generate tests based on counterexamples produced from modifications

      var programModifications = GetModifications(program).ToList();
      foreach (var modification in programModifications) {

        var log = await modification.GetCounterExampleLog();
        if (log == null) {
          continue;
        }
        var testMethod = await modification.GetTestMethod(dafnyInfo);
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
      var source = new StreamReader(sourceFile).ReadToEnd();
      var program = Utils.Parse(options, source, sourceFile);
      if (program == null) {
        yield break;
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

      var methodsGenerated = 0;
      await foreach (var method in GetTestMethodsForProgram(program)) {
        yield return method.ToString();
        methodsGenerated++;
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