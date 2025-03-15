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

  public static class TestGenerator {

    public static bool SetNonZeroExitCode = false;

    /// <summary>
    /// This method returns each capturedState that is unreachable, one by one,
    /// and then a line with the summary of how many such states there are, etc.
    /// Note that loop unrolling may cause false positives and the absence of
    /// loop unrolling may cause false negatives.
    /// </summary>
    /// <returns></returns>
    public static async IAsyncEnumerable<string> GetDeadCodeStatistics(Program program, Modifications cache) {
      lock (program.Options.ProverOptions) {
        program.Options.ProcessSolverOptions(new ConsoleErrorReporter(program.Options), Token.Cli);
      }
      if (program.Options.Printer is NullPrinter) {
        program.Options.Printer = new DafnyConsolePrinter(program.Options);
      }

      program.Reporter.Options.PrintMode = PrintModes.Everything;

      HashSet<string> allStates = [];
      HashSet<string> allDeadStates = [];

      // Generate tests based on counterexamples produced from modifications
      foreach (var modification in GetModifications(cache, program, out _)) {
        await modification.GetCounterExampleLog(cache);
        var deadStates = new HashSet<string>();
        if (!modification.IsCovered(cache)) {
          deadStates = modification.CapturedStates;
        }

        if (deadStates.Count != 0) {
          foreach (var capturedState in deadStates) {
            yield return $"Code at {capturedState} is potentially unreachable.";
          }
          allDeadStates.UnionWith(deadStates);
        }

        foreach (var state in modification.CapturedStates) {
          if (deadStates.Count == 0 && !allStates.Contains(state)) {
            yield return $"Code at {state} is reachable.";
          }
          allStates.Add(state);
        }
      }

      yield return $"Out of {allStates.Count} basic blocks, {allStates.Count - allDeadStates.Count} are reachable.";
    }

    public static async IAsyncEnumerable<string> GetDeadCodeStatistics(TextReader source, Uri uri, DafnyOptions options, CoverageReport report = null) {
      options.PrintMode = PrintModes.Everything;
      var code = await source.ReadToEndAsync();
      var firstPass = new FirstPass(options);
      if (!(await firstPass.IsOk(code, uri))) {
        SetNonZeroExitCode = true;
        yield break;
      }
      SetNonZeroExitCode = firstPass.NonZeroExitCode;
      var program = await Utils.Parse(new BatchErrorReporter(options), code, false, uri);
      if (report != null) {
        report.RegisterFiles(program); // do this here prior to modifying the program
      }
      var cache = new Modifications(program.Options);
      await foreach (var line in GetDeadCodeStatistics(program, cache)) {
        yield return line;
      }
      PopulateCoverageReport(report, program, cache);
    }

    /// <summary>
    /// Dafny to Boogie translator discards any methods/functions that do not have any verification goals
    /// By adding a trivial assertions in all {:testEntry}-annotated methods and function we ensure that
    /// they are not discarded during translation and we can still generate tests for them.
    /// </summary>
    private static void AddVerificationGoalsToEntryPoints(Program program) {
      foreach (var entryPoint in Utils.AllMemberDeclarationsWithAttribute(program.DefaultModule,
                 TestGenerationOptions.TestEntryAttribute)) {
        var trivialAssertion = new AssertStmt(entryPoint.Origin, new LiteralExpr(entryPoint.StartToken, true), null, null);
        if (entryPoint is Method method && method.Body != null && method.Body?.Body != null) {
          method.Body.Body.Insert(0, trivialAssertion);
        } else if (entryPoint is Function function && function.Body != null) {
          function.Body = new StmtExpr(entryPoint.StartToken, trivialAssertion, function.Body);
        }
      }
    }

    private static IEnumerable<ProgramModification> GetModifications(Modifications cache, Program program, out DafnyInfo dafnyInfo) {
      var options = program.Options;
      AddVerificationGoalsToEntryPoints(program);
      var success = Inlining.InliningTranslator.TranslateForFutureInlining(program, options, out var boogieProgram);
      dafnyInfo = null;
      if (!success) {
        options.ErrorWriter.WriteLine(
          $"*** Error: Failed at resolving or translating the inlined Dafny code.");
        SetNonZeroExitCode = true;
        return new List<ProgramModification>();
      }
      dafnyInfo = new DafnyInfo(program);
      // Create modifications of the program with assertions for each block\path
      ProgramModifier programModifier =
        options.TestGenOptions.Mode == TestGenerationOptions.Modes.Path
          ? new PathBasedModifier(cache)
          : new BlockBasedModifier(cache);
      return programModifier.GetModifications(boogieProgram, dafnyInfo);
    }

    private static void PopulateCoverageReport(CoverageReport coverageReport, Program program, Modifications cache) {
      if (coverageReport == null) {
        return;
      }

      var lineRegex = new Regex("^(.*)\\(([0-9]+),[0-9]+\\)");
      HashSet<string> coveredStates = []; // set of program states that are expected to be covered by tests
      foreach (var modification in cache.Values) {
        foreach (var preciseState in modification.CapturedStates) {
          if (modification.CounterexampleStatus == ProgramModification.Status.Success) {
            var index = preciseState.LastIndexOf('#');
            var state = index == -1 ? preciseState : preciseState[..index];
            coveredStates.Add(state);
          }
        }
      }
      Dictionary<Uri, Dictionary<int, CoverageLabel>> lineCoverageLabels = new();
      foreach (var modification in cache.Values) {
        foreach (var preciseState in modification.CapturedStates) {
          var index = preciseState.LastIndexOf('#');
          var state = index == -1 ? preciseState : preciseState[..index];
          var match = lineRegex.Match(state);
          if (!match.Success) {
            continue;
          }
          if (!int.TryParse(match.Groups[2].Value, out var lineNumber) || lineNumber == 0) {
            continue;
          }
          Uri uri;
          try {
            uri = new Uri(
              Path.IsPathRooted(match.Groups[1].Value)
                ? match.Groups[1].Value
                : Path.Combine(Directory.GetCurrentDirectory(), match.Groups[1].Value));
          } catch (ArgumentException) {
            continue;
          }
          if (!lineCoverageLabels.ContainsKey(uri)) {
            lineCoverageLabels[uri] = new Dictionary<int, CoverageLabel>();
          }
          var newLabel = coveredStates.Contains(state)
            ? CoverageLabel.FullyCovered
            : CoverageLabel.NotCovered;
          var oldLabel = lineCoverageLabels[uri].GetValueOrDefault(lineNumber, CoverageLabel.None);
          lineCoverageLabels[uri][lineNumber] = CoverageLabelExtension.Combine(newLabel, oldLabel);
        }
      }

      foreach (var uri in lineCoverageLabels.Keys) {
        foreach (var lineNumber in lineCoverageLabels[uri].Keys) {
          var rangeToken = new TokenRange(
              new Token(lineNumber, 1) { Uri = uri },
              new Token(lineNumber + 1, 1));
          coverageReport.LabelCode(rangeToken,
            lineCoverageLabels[uri][lineNumber]);
        }
      }
    }

    /// <summary>
    /// Generate test methods for a certain Dafny program.
    /// </summary>
    /// <returns></returns>
    public static async IAsyncEnumerable<TestMethod> GetTestMethodsForProgram(Program program, Modifications cache = null) {
      if (program.Options.Printer is NullPrinter) {
        program.Options.Printer = new DafnyConsolePrinter(program.Options);
      }

      lock (program.Options.ProverOptions) {
        program.Options.ProcessSolverOptions(new ConsoleErrorReporter(program.Options), Token.Cli);
      }

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
    public static async IAsyncEnumerable<string> GetTestClassForProgram(TextReader source, Uri uri, DafnyOptions options, CoverageReport report = null) {
      options.PrintMode = PrintModes.Everything;
      var code = await source.ReadToEndAsync();
      var firstPass = new FirstPass(options);
      if (!(await firstPass.IsOk(code, uri))) {
        SetNonZeroExitCode = true;
        yield break;
      }
      SetNonZeroExitCode = firstPass.NonZeroExitCode;
      var program = await Utils.Parse(new BatchErrorReporter(options), code, false, uri);
      var rawName = Regex.Replace(uri?.AbsolutePath ?? "", "[^a-zA-Z0-9_]", "");

      string EscapeDafnyStringLiteral(string str) {
        return $"\"{str.Replace(@"\", @"\\")}\"";
      }

      if (uri != null) {
        yield return $"include {EscapeDafnyStringLiteral(uri.AbsolutePath)}";
      }

      yield return $"module {rawName}UnitTests {{";

      var cache = new Modifications(options);
      var methodsGenerated = 0;
      DafnyInfo dafnyInfo = null;
      if (report != null) {
        report.RegisterFiles(program);
      }
      await foreach (var method in GetTestMethodsForProgram(program, cache)) {
        if (methodsGenerated == 0) {
          dafnyInfo = new DafnyInfo(program);
          foreach (var module in dafnyInfo.ToImportAs.Keys) {
            if (module.Split(".").Last() == dafnyInfo.ToImportAs[module]) {
              yield return $"import {module}";
            } else {
              yield return $"import {dafnyInfo.ToImportAs[module]} = {module}";
            }
          }
        }
        yield return method.ToString();
        methodsGenerated++;
      }

      yield return TestMethod.EmitSynthesizeMethods(dafnyInfo, cache);
      yield return "}";

      PopulateCoverageReport(report, program, cache);

      if (methodsGenerated == 0) {
        await options.ErrorWriter.WriteLineAsync(
          "*** Error: No tests were generated, because no code points could be " +
          "proven reachable (do you have a false assumption in the program?)");
        SetNonZeroExitCode = true;
      }
    }
  }
}
