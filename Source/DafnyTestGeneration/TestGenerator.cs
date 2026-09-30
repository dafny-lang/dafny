// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;

namespace DafnyTestGeneration {

  public static class TestGenerator {

    public static bool SetNonZeroExitCode = false;
    private static readonly Dictionary<string, List<string>> IgnoreNames = [];
    private static readonly Dictionary<string, List<string>> LengthNames = [];
    private static readonly Dictionary<string, BlockStmt> OriginalBodies = [];
    private static readonly Dictionary<string, (List<AttributedExpression>, List<AttributedExpression>)> OriginalSpec = [];

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
          : options.TestGenOptions.Mode == TestGenerationOptions.Modes.Spec
            ? new SpecBasedModifier(cache)
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

      List<TestMethod> testMethods = new List<TestMethod>();

      PrepareProgram(program, options.TestGenOptions.Mode == TestGenerationOptions.Modes.Spec);

      for (int i = 0; i < options.TestGenOptions.Repeat; i++) {
        testMethods.Clear();

        Modifications currentCache = (i == 0)
          ? (cache ?? new Modifications(options))
          : new Modifications(program.Options);

        foreach (var modification in GetModifications(currentCache, program, out var dafnyInfo)) {

          var log = await modification.GetCounterExampleLog(currentCache);
          if (log == null) {
            continue;
          }

          var testMethod = await modification.GetTestMethod(currentCache, dafnyInfo);
          if (testMethod == null) {
            continue;
          }

          yield return testMethod;
          testMethods.Add(testMethod);
        }

        if (testMethods.Count == 0) {
          break;
        }

        if (options.TestGenOptions.Time) {
          await options.OutputWriter.Status(
            $"\n// REPEAT {i + 1} - TIME: {options.TestGenOptions.StopWatch.Elapsed.TotalSeconds} s\n");
        }

        if (i < options.TestGenOptions.Repeat - 1) {
          program = await UpdateProgram(program, testMethods);
          if (!Utils.AllMemberDeclarations(program.DefaultModule).Any()) {
            break;
          }
        }
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
      AddTestEntryAttribute(program);
      var rawName = Regex.Replace(uri?.AbsolutePath ?? "", "[^a-zA-Z0-9_]", "");
      var isWrappedInAModule = CheckIsWrappedInAModule(program);

      string EscapeDafnyStringLiteral(string str) {
        return $"\"{str.Replace(@"\", @"\\")}\"";
      }

      if (uri != null) {
        yield return $"include {EscapeDafnyStringLiteral(uri.AbsolutePath)}";
      }

      if (isWrappedInAModule) {
        yield return $"module {rawName}UnitTests {{";
      }

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
      if (isWrappedInAModule) {
        yield return "}";
      }

      PopulateCoverageReport(report, program, cache);

      if (methodsGenerated == 0) {
        await options.ErrorWriter.WriteLineAsync(
          "*** Error: No tests were generated, because no code points could be " +
          "proven reachable (do you have a false assumption in the program?)");
        SetNonZeroExitCode = true;
      }
    }

    /// <summary>
    /// Return true iff the program has no elements that are not wrapped in a module
    /// (so all elements can be imported provided the export sets allow it)
    /// </summary>
    private static bool CheckIsWrappedInAModule(Program program) {
      if (program.DefaultModuleDef.Children.OfType<ClassLikeDecl>().Any() || program.DefaultModuleDef.Children.OfType<DefaultClassDecl>().Any(decl => decl.Children.Any())) {
        return false;
      }
      return true;
    }

    /// <summary>
    /// Updates the program for the Spec test generation mode, given the input parameters previously generated
    /// for each testMethod.
    /// </summary>
    private static async Task<Program> UpdateProgram(Program program, List<TestMethod> testMethods) {
      // Turn off BVA so it does not attempt the same values
      program.Options.TestGenOptions.Bva = null;

      // Delete method duplicates of functions
      foreach (var module in program.Modules()) {
        foreach (var decl in module.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {

          var functionNames = new HashSet<string>();

          foreach (var func in decl.Members.OfType<Function>()) {
            functionNames.Add(func.Name);
            func.ByMethodBody = null;
            func.ByMethodDecl = null;
            func.ByMethodTok = null;
          }

          decl.Members.RemoveAll(member =>
            member is Method method && functionNames.Contains(method.Name)
          );

          foreach (var method in decl.Members.OfType<Method>()) {
            if (OriginalBodies.TryGetValue(method.Name, out BlockStmt body)) {
              method.SetBody(body);
            }
            if (OriginalSpec.TryGetValue(method.Name, out var spec)) {
              method.Req = spec.Item1;
              method.Ens = spec.Item2;
            }
          }
        }
      }

      var entryPointsToDelete = new HashSet<MemberDecl>();

      foreach (var entryPoint in Utils.AllMemberDeclarationsWithAttribute(program.DefaultModule,
                 TestGenerationOptions.TestEntryAttribute)) {
        bool insertedAssume = false;

        for (var i = testMethods.Count - 1; i >= 0; i--) {
          var testMethod = testMethods[i];
          var shortName = testMethod.MethodName.Contains('.')
            ? testMethod.MethodName.Substring(testMethod.MethodName.LastIndexOf('.') + 1)
            : testMethod.MethodName;

          if (entryPoint.Name != shortName) {
            continue;
          }

          List<Formal> argFormals;

          switch (entryPoint) {
            case Method methodDecl:
              argFormals = methodDecl.Ins.ToList();
              break;
            case Function functionDecl:
              argFormals = functionDecl.Ins.ToList();
              break;
            default: return program;
          }


          foreach (var formal in argFormals) {
            if ((!IgnoreNames.TryGetValue(entryPoint.Name, out var ignoredForEntry) || !ignoredForEntry.Contains(formal.Name)) && testMethod.ArgExpressions.TryGetValue(formal.Name, out var argExpr) && argExpr != null) {
              var validTok = entryPoint.StartToken;

              var nameSegment = new NameSegment(validTok, formal.Name, null);

              List<Expression> allConstraints = [];

              if (LengthNames.TryGetValue(entryPoint.Name, out var lengthEntry) && lengthEntry.Contains(formal.Name)) {
                var cardinality = new UnaryOpExpr(validTok, UnaryOpExpr.Opcode.Cardinality, nameSegment);
                var literalExpr = new LiteralExpr(validTok, argExpr.Children.Count());
                allConstraints.Add(new BinaryExpr(validTok, BinaryExpr.Opcode.Neq, cardinality, literalExpr));
              } else {
                allConstraints.Add(new BinaryExpr(validTok, BinaryExpr.Opcode.Neq, nameSegment, argExpr));
                allConstraints.AddRange(Utils.GetNestedConstraints(nameSegment, argExpr, validTok));
              }

              var axiomAttr = new Attributes(Attributes.AxiomAttributeName, [], null);

              foreach (var constraint in allConstraints) {
                var assumeStmt = new AssumeStmt(validTok, constraint, axiomAttr);
                insertedAssume = true;
                if (entryPoint is Method method) {
                  if (method.Body != null) {
                    method.Body.Body.Insert(0, assumeStmt);
                    if (OriginalBodies.TryGetValue(method.Name, out var body)) {
                      body.Body.Insert(0, assumeStmt);
                    }
                  } else {
                    method.SetBody(new BlockStmt(validTok, [assumeStmt]));
                  }
                } else if (entryPoint is Function function) {
                  function.Body = new StmtExpr(validTok, assumeStmt, function.Body);
                }
              }
            }
          }
          testMethods.RemoveAt(i);
        }
        if (!insertedAssume) {
          entryPointsToDelete.Add(entryPoint);
        }
      }

      if (entryPointsToDelete.Count > 0) {
        foreach (var module in program.Modules()) {
          foreach (var decl in module.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
            decl.Members.RemoveAll(member => entryPointsToDelete.Contains(member));
          }
        }
      }

      return await Utils.GetFreshProgram(program);
    }

    /// <summary>
    /// Adds {:testEntry} attribute to methods and functions that are known to have failed the verification step.
    /// </summary>
    private static void AddTestEntryAttribute(Program program) {
      var failedMembers = program.Options.TestGenOptions.FailedVerification;

      foreach (var member in Utils.AllMemberDeclarations(program.DefaultModule)) {
        bool isFailedMember = failedMembers.Any(f =>
          f == member.Name || f.EndsWith("." + member.Name));

        if (member is Method { IsGhost: false } or Function { IsGhost: false }) {
          if (isFailedMember && !member.HasUserAttribute(TestGenerationOptions.TestEntryAttribute, out _)) {
            member.Attributes = new Attributes(
              TestGenerationOptions.TestEntryAttribute,
              [],
              member.Attributes
            );
          }
        }
      }
    }

    /// <summary>
    /// Deletes the implementation of the methods that will be tested, as this information is not useful
    /// for specification-based test generation, and can be conflicting with the following steps.
    /// </summary>
    private static void PrepareProgram(Program program, bool isSpecMode) {
      foreach (var entryPoint in Utils.AllMemberDeclarationsWithAttribute(program.DefaultModule,
                 TestGenerationOptions.TestEntryAttribute)) {

        if (entryPoint is Method method) {

          var cloner = new Cloner();
          var copiedReq = method.Req.Select(req =>
            new AttributedExpression(cloner.CloneExpr(req.E), req.Label, req.Attributes)
          ).ToList();
          var copiedEns = method.Ens.Select(ens =>
            new AttributedExpression(cloner.CloneExpr(ens.E), ens.Label, ens.Attributes)
          ).ToList();
          OriginalSpec[method.Name] = (copiedReq, copiedEns);

          if (method.Body is not null) {
            if (isSpecMode) {
              method.SetBody(new BlockStmt(method.Body.Origin, []));
            } else {
              OriginalBodies[method.Name] = cloner.CloneBlockStmt(method.Body);
            }
          }

          foreach (var formal in method.Ins) {
            switch (formal.Type) {
              case UserDefinedType { Name: "string" or "nat" }:
                break;
              case UserDefinedType tupleType when tupleType.Name.StartsWith("_tuple#"):
                var tupleArgs = tupleType.TypeArgs;
                if (tupleArgs.Any(arg => arg is UserDefinedType { Name: not "string" and not "nat" } udt &&
                                         !udt.Name.StartsWith("_tuple#"))) {
                  if (IgnoreNames.TryGetValue(method.Name, out var ignoreTupleList)) {
                    ignoreTupleList.Add(formal.Name);
                  } else {
                    IgnoreNames[method.Name] = [formal.Name];
                  }
                }
                break;
              case UserDefinedType:
                if (IgnoreNames.TryGetValue(method.Name, out var ignoreList)) {
                  ignoreList.Add(formal.Name);
                } else {
                  IgnoreNames[method.Name] = [formal.Name];
                }
                break;
              case SeqType seqType:
                var seqArg = seqType.Arg;
                if (seqArg is UserDefinedType) {
                  if (LengthNames.TryGetValue(method.Name, out var lengthList)) {
                    lengthList.Add(formal.Name);
                  } else {
                    LengthNames[method.Name] = [formal.Name];
                  }
                }
                break;
              case SetType setType:
                var setArg = setType.Arg;
                if (setArg is UserDefinedType) {
                  if (LengthNames.TryGetValue(method.Name, out var lengthList)) {
                    lengthList.Add(formal.Name);
                  } else {
                    LengthNames[method.Name] = [formal.Name];
                  }
                }
                break;
              case MapType mapType:
                var mapArg = mapType.Arg;
                if (mapArg is UserDefinedType) {
                  if (LengthNames.TryGetValue(method.Name, out var lengthList)) {
                    lengthList.Add(formal.Name);
                  } else {
                    LengthNames[method.Name] = [formal.Name];
                  }
                }
                break;
            }
          }
        }
      }
    }
  }
}
