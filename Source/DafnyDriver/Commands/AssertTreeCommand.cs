#nullable enable
using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using DafnyCore;
using DafnyCore.Options;
using DafnyDriver.Commands;
using Microsoft.Boogie;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny;

public class AssertFinder : ASTVisitor<IASTVisitorContext> {
  private List<AssertStmt> asserts = new List<AssertStmt>();

  public override IASTVisitorContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
    return astVisitorContext; // Reuse the provided context
  }
  protected override void VisitStatement(Statement stmt, IASTVisitorContext context) {
    if (stmt is AssertStmt assertStmt) {
        asserts.Add(assertStmt);
        // Cannot find a way of doing this better nevertheless if assert ends in ; is normal
        // if assdrtion ends in "}" it a a by assertion
        //Console.WriteLine($"Start: {assertStmt.StartToken} End:{assertStmt.EndToken}");
        var assertendsymbol = assertStmt.EndToken.val;
        var type = "Regular_assertion";
        if(assertendsymbol == ";"){
          type = "Regular_assertion";
          // Regular assertion
        } else {
          type = "By_assertion";
          // Multi line by assertion
        }
        Console.WriteLine($"    <assertion>");
        Console.WriteLine($"      <type>{type} </type>");
        Console.WriteLine($"      <start_pos>{assertStmt.StartToken.pos} </start_pos>");
        Console.WriteLine($"      <end_pos>{assertStmt.EndToken.pos} </end_pos>"); 
        Console.WriteLine($"    </assertion>");
        //Console.WriteLine($"  (Type_of_assertion={type},Star_pos={assertStmt.StartToken.pos},End_pos={assertStmt.EndToken.pos})");
        // Token toString
        //public override string ToString() {
        //return $"'{val}': {Path.GetFileName(Filepath)}@{pos} - @{line}:{col}";
        //}
    }
    base.VisitStatement(stmt, context);
  }

  public override void VisitFunction(Function function) {  
      Console.WriteLine($"  <Function>");
      Console.WriteLine($"    <name> {function.FullName} </name>");
      Console.WriteLine($"    <start_pos> {function.StartToken.pos} </start_pos>");
      Console.WriteLine($"    <end_pos> {function.EndToken.pos} </end_pos>");
      base.VisitFunction(function);
      Console.WriteLine($"  </Function>");
  }

  public override void VisitMethod(Method method) {
      Console.WriteLine($"  <Method>");
      Console.WriteLine($"    <name> {method.FullName} </name>");
      Console.WriteLine($"    <start_pos> {method.StartToken.pos} </start_pos>");
      Console.WriteLine($"    <end_pos> {method.EndToken.pos} </end_pos>");
      base.VisitMethod(method);
      Console.WriteLine($"  </Method>");
  }
  public List<AssertStmt> GetAllAsserts() {
    return asserts;
  }
}

public static class AssertTreeCommand {

  static AssertTreeCommand() {
  }

  public static Command Create() {
    var result = new Command("asserttree", "Create program Assert XML tree.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in VerifyOptions) {
      result.AddOption(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => HandleVerification(options));
    return result;
  }

  private static IReadOnlyList<Option> VerifyOptions =>
    new Option[] {
        DafnyFile.DoNotVerifyDependencies
      }.Concat(DafnyCommands.VerificationOptions).
      Concat(DafnyCommands.ConsoleOutputOptions).
      Concat(DafnyCommands.ResolverOptions);

  public static async Task<int> HandleVerification(DafnyOptions options) {
    if (options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
      options.TrackVerificationCoverage = true;
    }

    var compilation = CliCompilation.Create(options);
    compilation.Start();

    var resolution = await compilation.Resolution;
    if (resolution != null) {
      var resolvedProgram = resolution.ResolvedProgram;
      if (resolvedProgram == null) {
        return 1;
      }
      Console.WriteLine($"<program>");
      Console.WriteLine($"  <name>{resolvedProgram.Name}</name>");
      foreach (var module in resolvedProgram.Modules()) {
        if (module != null && module.TopLevelDecls != null) {
          var assertFinder = new AssertFinder(); 
          assertFinder.VisitDeclarations(module.TopLevelDecls.ToList());
          var allAsserts = assertFinder.GetAllAsserts();
        }
      }
      Console.WriteLine($"</program>");
    }
    return await compilation.GetAndReportExitCode();
  }

  public static async Task ReportVerificationSummary(
    CliCompilation cliCompilation,
    IObservable<CanVerifyResult> verificationResults) {
    var statistics = new VerificationStatistics();

    verificationResults.Subscribe(result => {
      foreach (var taskResult in result.Results) {
        var runResult = taskResult.Result;
        Interlocked.Add(ref statistics.TotalResourcesUsed, runResult.ResourceCount);
        lock (statistics) {
          statistics.MaxVcResourcesUsed = Math.Max(statistics.MaxVcResourcesUsed, runResult.ResourceCount);
        }

        switch (runResult.Outcome) {
          case SolverOutcome.Valid:
          case SolverOutcome.Bounded:
            Interlocked.Increment(ref statistics.VerifiedSymbols);
            Interlocked.Add(ref statistics.VerifiedAssertions, runResult.Asserts.Count);
            break;
          case SolverOutcome.Invalid:
            var total = runResult.Asserts.Count;
            var errors = runResult.CounterExamples.Count;
            Interlocked.Add(ref statistics.VerifiedAssertions, total - errors);
            Interlocked.Add(ref statistics.ErrorCount, errors);
            break;
          case SolverOutcome.TimeOut:
            Interlocked.Increment(ref statistics.TimeoutCount);
            break;
          case SolverOutcome.OutOfMemory:
            Interlocked.Increment(ref statistics.OutOfMemoryCount);
            break;
          case SolverOutcome.OutOfResource:
            Interlocked.Increment(ref statistics.OutOfResourceCount);
            break;
          case SolverOutcome.Undetermined:
            Interlocked.Increment(ref statistics.InconclusiveCount);
            break;
          default:
            throw new ArgumentOutOfRangeException();
        }
      }
    }, e => {
      Interlocked.Increment(ref statistics.SolverExceptionCount);
    });
    await verificationResults.WaitForComplete();
    await WriteTrailer(cliCompilation, statistics);
  }

  private static async Task WriteTrailer(CliCompilation cliCompilation,
    VerificationStatistics statistics) {
    if (cliCompilation.Options.Verbosity <= CoreOptions.VerbosityLevel.Quiet) {
      return;
    }
    if (!cliCompilation.DidVerification) {
      return;
    }
    var output = cliCompilation.Options.OutputWriter;
    await output.WriteLineAsync();
    await output.WriteLineAsync();
    await output.FlushAsync();
  }

  public static void ReportVerificationDiagnostics(CliCompilation compilation, IObservable<CanVerifyResult> verificationResults) {
    verificationResults.Subscribe(result => {
      // We use an intermediate reporter so we can sort the diagnostics from all parts by token
      var batchReporter = new BatchErrorReporter(compilation.Options);
      foreach (var completed in result.Results) {
        Compilation.ReportDiagnosticsInResult(compilation.Options, result.CanVerify.FullDafnyName,
          BoogieGenerator.ToDafnyToken(true, completed.Task.Token),
          (uint)completed.Result.RunTime.TotalSeconds,
          completed.Result, batchReporter);
      }

      foreach (var diagnostic in batchReporter.AllMessages.Order()) {
        compilation.Compilation.Reporter.Message(diagnostic.Source, diagnostic.Level, diagnostic.ErrorId, diagnostic.Token,
          diagnostic.Message);
      }
    });
  }

  public static async Task LogVerificationResults(CliCompilation cliCompilation, ResolutionResult resolution,
    IObservable<CanVerifyResult> verificationResults) {
    VerificationResultLogger? verificationResultLogger = null;
    var proofDependencyManager = resolution.ResolvedProgram.ProofDependencyManager;
    try {
      verificationResultLogger = new VerificationResultLogger(cliCompilation.Options, proofDependencyManager);
    } catch (ArgumentException e) {
      cliCompilation.Compilation.Reporter.Error(MessageSource.Verifier, cliCompilation.Compilation.Project.StartingToken, e.Message);
    }

    verificationResults.Subscribe(result => verificationResultLogger?.Report(result),
      e => { },
      () => {
      });
    await verificationResults.WaitForComplete();
    if (verificationResultLogger != null) {
      await verificationResultLogger.Finish();
    }
  }

  public static async Task ReportProofDependencies(
    CliCompilation cliCompilation,
    ResolutionResult resolution,
    IObservable<CanVerifyResult> verificationResults) {
    var usedDependencies = new HashSet<TrackedNodeComponent>();
    var proofDependencyManager = resolution.ResolvedProgram.ProofDependencyManager;

    verificationResults.Subscribe(result => {
      ProofDependencyWarnings.ReportSuspiciousDependencies(cliCompilation.Options, result.Results,
        resolution.ResolvedProgram.Reporter, resolution.ResolvedProgram.ProofDependencyManager);

      foreach (var used in result.Results.SelectMany(part => part.Result.CoveredElements)) {
        usedDependencies.Add(used);
      }
    }, e => { }, () => { });
    await verificationResults.WaitForComplete();
    var coverageReportDir = cliCompilation.Options.Get(CommonOptionBag.VerificationCoverageReport);
    if (coverageReportDir != null) {
      await new CoverageReporter(cliCompilation.Options).SerializeVerificationCoverageReport(
        proofDependencyManager, resolution.ResolvedProgram,
        usedDependencies,
        coverageReportDir);
    }
  }
}

