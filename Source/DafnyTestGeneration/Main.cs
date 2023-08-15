// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

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

    public static bool SetNonZeroExitCode = false;

    /// <summary>
    /// This method returns each capturedState that is unreachable, one by one,
    /// and then a line with the summary of how many such states there are, etc.
    /// Note that loop unrolling may cause false positives and the absence of
    /// loop unrolling may cause false negatives.
    /// </summary>
    /// <returns></returns>
    public static async IAsyncEnumerable<string> GetDeadCodeStatistics(Program program, Modifications cache) {

      program.Reporter.Options.PrintMode = PrintModes.Everything;

      var blocksReached = 0;
      HashSet<string> allStates = new();
      HashSet<string> allDeadStates = new();

      // Generate tests based on counterexamples produced from modifications
      foreach (var modification in GetModifications(cache, program, out _)) {
        blocksReached++;
        await modification.GetCounterExampleLog(cache);
        var deadStates = new HashSet<string>();
        if (!modification.IsCovered(cache)) {
          deadStates = modification.CapturedStates;
        }

        if (deadStates.Count != 0) {
          foreach (var capturedState in deadStates) {
            yield return $"Code at {capturedState} is potentially unreachable.";
          }
          blocksReached--;
          allDeadStates.UnionWith(deadStates);
        }

        foreach (var state in modification.CapturedStates) {
          if (!allStates.Contains(state)) {
            yield return $"Code at {state} is reachable.";
            allStates.Add(state);
          }
        }
      }

      yield return $"Out of {blocksReached} basic blocks " +
                   $"({allStates.Count} capturedStates), {blocksReached} " +
                   $"({allStates.Count - allDeadStates.Count}) are reachable. " +
                   "There might be false negatives if you are not unrolling " +
                   "loops. False positives are always possible.";
    }

    public static async IAsyncEnumerable<string> GetDeadCodeStatistics(string sourceFile, DafnyOptions options, CoverageReport report) {
      options.PrintMode = PrintModes.Everything;
      var source = await new StreamReader(sourceFile).ReadToEndAsync();
      var program = Utils.Parse(options, source, false, new Uri(sourceFile));
      if (program == null) {
        yield return "Cannot parse program";
        yield break;
      }
      if (Utils.ProgramHasAttribute(program,
            TestGenerationOptions.TestInlineAttribute)) {
        options.VerifyAllModules = true;
      }
      var cache = new Modifications(program.Options);
      await foreach (var line in GetDeadCodeStatistics(program, cache)) {
        yield return line;
      }
      PopulateCoverageReport(report, program, cache);
    }

    private static IEnumerable<ProgramModification> GetModifications(Modifications cache, Program program, out DafnyInfo dafnyInfo) {
      var options = program.Options;
      var success = Inlining.InliningTranslator.TranslateForFutureInlining(program, options, out var boogieProgram);
      dafnyInfo = null;
      if (!success) {
        options.Printer.ErrorWriteLine(options.ErrorWriter,
          $"Error: Failed at resolving or translating the inlined Dafny code.");
        SetNonZeroExitCode = true;
        return new List<ProgramModification>();
      }
      dafnyInfo = new DafnyInfo(program);
      SetNonZeroExitCode = dafnyInfo.SetNonZeroExitCode || SetNonZeroExitCode;
      if (!Utils.ProgramHasAttribute(program,
            TestGenerationOptions.TestEntryAttribute)) {
        options.Printer.ErrorWriteLine(options.ErrorWriter,
          $"Error: Found no methods or functions annotated with {TestGenerationOptions.TestEntryAttribute}. " +
          $"Please annotate all entry points for testing with this attribute.");
        SetNonZeroExitCode = true;
        return new List<ProgramModification>();
      }
      // Create modifications of the program with assertions for each block\path
      ProgramModifier programModifier =
        options.TestGenOptions.Mode == TestGenerationOptions.Modes.Path
          ? new PathBasedModifier(cache)
          : new BlockBasedModifier(cache);
      return programModifier.GetModifications(boogieProgram, dafnyInfo);
    }

    private static void PopulateCoverageReport(CoverageReport coverageReport, Program program, Modifications cache) {
      coverageReport.RegisterFiles(program);
      var lineRegex = new Regex("^(.*)\\(([0-9]+),[0-9]+\\)");
      HashSet<string> coveredStates = new(); // set of program states that are expected to be covered by tests
      foreach (var modification in cache.Values) {
        foreach (var state in modification.CapturedStates) {
          if (modification.CounterexampleStatus == ProgramModification.Status.Success) {
            coveredStates.Add(state);
          }
        }
      }
      foreach (var modification in cache.Values) {
        foreach (var state in modification.CapturedStates) {
          var match = lineRegex.Match(state);
          if (!match.Success) {
            continue;
          }
          if (!int.TryParse(match.Groups[2].Value, out var lineNumber) || lineNumber == 0) {
            continue;
          }
          lineNumber -= 1; // to zero-based
          Uri uri;
          try {
            uri = new Uri(
              Path.IsPathRooted(match.Groups[1].Value)
                ? match.Groups[1].Value
                : Path.Combine(Directory.GetCurrentDirectory(), match.Groups[1].Value));
          } catch (ArgumentException) {
            continue;
          }
          var rangeToken = new RangeToken(new Token(lineNumber, 0), new Token(lineNumber + 1, 0));
          rangeToken.Uri = uri;
          coverageReport.LabelCode(rangeToken,
            coveredStates.Contains(state)
              ? CoverageLabel.FullyCovered
              : CoverageLabel.NotCovered);
        }
      }
    }

    /// <summary>
    /// Generate test methods for a certain Dafny program.
    /// </summary>
    /// <returns></returns>
    public static async IAsyncEnumerable<TestMethod> GetTestMethodsForProgram(Program program, Modifications cache = null) {

      var options = program.Options;
      options.PrintMode = PrintModes.Everything;
      // Generate tests based on counterexamples produced from modifications

      cache ??= new Modifications(options);
      foreach (var modification in GetModifications(cache, program, out var dafnyInfo)) {

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
    }

    /// <summary>
    /// Return a Dafny class (list of lines) with tests for the given Dafny file
    /// </summary>
    public static async IAsyncEnumerable<string> GetTestClassForProgram(string sourceFile, DafnyOptions options, CoverageReport report) {
      options.PrintMode = PrintModes.Everything;
      TestMethod.ClearTypesToSynthesize();
      var source = await new StreamReader(sourceFile).ReadToEndAsync();
      var uri = new Uri(sourceFile);
      var program = Utils.Parse(options, source, true, uri);
      if (program == null) {
        yield break;
      }
      if (Utils.ProgramHasAttribute(program,
            TestGenerationOptions.TestInlineAttribute)) {
        options.VerifyAllModules = true;
      }
      // Suppressing error messages which will be printed when dafnyInfo is initialized again in GetModifications
      var dafnyInfo = new DafnyInfo(program, true);
      program = Utils.Parse(options, source, false, uri);
      SetNonZeroExitCode = dafnyInfo.SetNonZeroExitCode || SetNonZeroExitCode;
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

      yield return TestMethod.EmitSynthesizeMethods(dafnyInfo);
      yield return "}";

      PopulateCoverageReport(report, program, cache);

      if (methodsGenerated == 0) {
        options.Printer.ErrorWriteLine(options.ErrorWriter,
          "Error: No tests were generated, because no code points could be " +
          "proven reachable (do you have a false assumption in the program?)");
        SetNonZeroExitCode = true;
      }
    }
  }
}
