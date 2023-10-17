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

      HashSet<string> allStates = new();
      HashSet<string> allDeadStates = new();

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
      if (!firstPass.IsOk(code, uri)) {
        SetNonZeroExitCode = true;
        yield break;
      }
      SetNonZeroExitCode = firstPass.NonZeroExitCode;
      var program = Utils.Parse(new BatchErrorReporter(options), code, false, uri);
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
        var trivialAssertion = new AssertStmt(entryPoint.RangeToken,
          new LiteralExpr(entryPoint.StartToken, true), null, null, null);
        if (entryPoint is Method method && method.Body != null && method.Body.Body != null) {
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
        options.Printer.ErrorWriteLine(options.ErrorWriter,
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

      var lineNumToPosCache = new Dictionary<Uri, int[]>();
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
          Uri uri;
          try {
            uri = new Uri(
              Path.IsPathRooted(match.Groups[1].Value)
                ? match.Groups[1].Value
                : Path.Combine(Directory.GetCurrentDirectory(), match.Groups[1].Value));
          } catch (ArgumentException) {
            continue;
          }
          var linePos = Utils.GetPosFromLine(uri, lineNumber, lineNumToPosCache);
          var lineLength = Utils.GetPosFromLine(uri, lineNumber + 1, lineNumToPosCache) - linePos - 1;
          var rangeToken = new RangeToken(new Token(lineNumber, 1), new Token(lineNumber, lineLength));
          rangeToken.Uri = uri;
          rangeToken.StartToken.pos = linePos;
          rangeToken.EndToken.pos = linePos + lineLength;
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
    public static async IAsyncEnumerable<string> GetTestClassForProgram(TextReader source, Uri uri, DafnyOptions options, CoverageReport report = null) {
      options.PrintMode = PrintModes.Everything;
      TestMethod.ClearTypesToSynthesize();
      var code = await source.ReadToEndAsync();
      var firstPass = new FirstPass(options);
      if (!firstPass.IsOk(code, uri)) {
        SetNonZeroExitCode = true;
        yield break;
      }
      SetNonZeroExitCode = firstPass.NonZeroExitCode;
      var program = Utils.Parse(new BatchErrorReporter(options), code, false, uri);
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
        report.RegisterFiles(program); // do this here prior to modifying the program
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

      yield return TestMethod.EmitSynthesizeMethods(dafnyInfo);
      yield return "}";

      PopulateCoverageReport(report, program, cache);

      if (methodsGenerated == 0) {
        options.Printer.ErrorWriteLine(options.ErrorWriter,
          "*** Error: No tests were generated, because no code points could be " +
          "proven reachable (do you have a false assumption in the program?)");
        SetNonZeroExitCode = true;
      }
    }
  }
}
