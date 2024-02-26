#nullable enable
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive.Subjects;
using System.Reactive.Threading.Tasks;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using Token = Microsoft.Dafny.Token;
using Util = Microsoft.Dafny.Util;

namespace DafnyDriver.Commands;

public record CanVerifyResult(ICanVerify CanVerify, IReadOnlyList<VerificationTaskResult> Results);

public class CliCompilation {
  private readonly DafnyOptions options;

  private Compilation Compilation { get; }
  private readonly ConcurrentDictionary<MessageSource, int> errorsPerSource = new();
  private int errorCount;
  private bool verifiedAssertions = false;

  private CliCompilation(
    CreateCompilation createCompilation,
    DafnyOptions options) {
    this.options = options;

    if (options.DafnyProject == null) {
      var firstFile = options.CliRootSourceUris.FirstOrDefault();
      var uri = firstFile ?? new Uri(Directory.GetCurrentDirectory());
      options.DafnyProject = new DafnyProject {
        Includes = Array.Empty<string>(),
        Uri = uri,
        ImplicitFromCli = true
      };
    }

    options.RunningBoogieFromCommandLine = true;

    var input = new CompilationInput(options, 0, options.DafnyProject);
    var executionEngine = new ExecutionEngine(options, new VerificationResultCache(), DafnyMain.LargeThreadScheduler);
    Compilation = createCompilation(executionEngine, input);
  }

  public int ExitCode => (int)ExitValue;

  public ExitValue ExitValue {
    get {
      if (HasErrorsFromSource(MessageSource.Project)) {
        return ExitValue.PREPROCESSING_ERROR;
      }

      if (HasErrorsFromSource(MessageSource.Verifier)) {
        return ExitValue.VERIFICATION_ERROR;
      }
      return errorCount > 0 ? ExitValue.DAFNY_ERROR : ExitValue.SUCCESS;

      bool HasErrorsFromSource(MessageSource source) {
        return errorsPerSource.GetOrAdd(source, _ => 0) != 0;
      }
    }
  }

  public Task<ResolutionResult> Resolution => Compilation.Resolution;

  public void Start() {
    if (Compilation.Started) {
      throw new InvalidOperationException("Compilation was already started");
    }

    ErrorReporter consoleReporter = options.DiagnosticsFormat switch {
      DafnyOptions.DiagnosticsFormats.PlainText => new ConsoleErrorReporter(options),
      DafnyOptions.DiagnosticsFormats.JSON => new JsonConsoleErrorReporter(options),
      _ => throw new ArgumentOutOfRangeException()
    };

    Compilation.Updates.Subscribe(ev => {
      if (ev is NewDiagnostic newDiagnostic) {
        if (newDiagnostic.Diagnostic.Level == ErrorLevel.Error) {
          errorsPerSource.AddOrUpdate(newDiagnostic.Diagnostic.Source,
            _ => 1,
            (_, previous) => previous + 1);
          Interlocked.Increment(ref errorCount);
        }
        var dafnyDiagnostic = newDiagnostic.Diagnostic;
        consoleReporter.Message(dafnyDiagnostic.Source, dafnyDiagnostic.Level,
          dafnyDiagnostic.ErrorId, dafnyDiagnostic.Token, dafnyDiagnostic.Message);
      } else if (ev is FinishedParsing finishedParsing) {
        if (errorCount > 0) {
          var programName = finishedParsing.Program.Name;
          options.OutputWriter.WriteLine($"{errorCount} parse errors detected in {programName}");
        }
      } else if (ev is FinishedResolution finishedResolution) {
        DafnyMain.MaybePrintProgram(finishedResolution.Result.ResolvedProgram, options.DafnyPrintResolvedFile, true);

        if (errorCount > 0) {
          var programName = finishedResolution.Result.ResolvedProgram.Name;
          options.OutputWriter.WriteLine($"{errorCount} resolution/type errors detected in {programName}");
        }
      }

    });
    Compilation.Start();
  }

  public static CliCompilation Create(DafnyOptions options) {
    var fileSystem = OnDiskFileSystem.Instance;
    ILoggerFactory factory = new LoggerFactory();
    var telemetryPublisher = new CliTelemetryPublisher(factory.CreateLogger<TelemetryPublisherBase>());
    return new CliCompilation(CreateCompilation, options);

    Compilation CreateCompilation(ExecutionEngine engine, CompilationInput input) =>
      new(factory.CreateLogger<Compilation>(), fileSystem,
        new TextDocumentLoader(factory.CreateLogger<ITextDocumentLoader>(),
          new DafnyLangParser(options, fileSystem, telemetryPublisher,
            factory.CreateLogger<DafnyLangParser>(),
            factory.CreateLogger<CachingParser>()),
          new DafnyLangSymbolResolver(factory.CreateLogger<DafnyLangSymbolResolver>(), factory.CreateLogger<CachingResolver>(), telemetryPublisher)),
        new DafnyProgramVerifier(factory.CreateLogger<DafnyProgramVerifier>()), engine, input);
  }

  public void RecordProofDependencies(ResolutionResult resolution) {
    var usedDependencies = new HashSet<TrackedNodeComponent>();
    var proofDependencyManager = resolution.ResolvedProgram.ProofDependencyManager;
    VerificationResultLogger? verificationResultLogger = null;
    try {
      verificationResultLogger = new VerificationResultLogger(options, proofDependencyManager);
    } catch (ArgumentException e) {
      Compilation.Reporter.Error(MessageSource.Verifier, Compilation.Project.StartingToken, e.Message);
    }

    verificationResults.Subscribe(result => {

      ProofDependencyWarnings.ReportSuspiciousDependencies(options, result.Results,
        resolution.ResolvedProgram.Reporter, resolution.ResolvedProgram.ProofDependencyManager);

      verificationResultLogger?.Report(result);

      foreach (var used in result.Results.SelectMany(part => part.Result.CoveredElements)) {
        usedDependencies.Add(used);
      }
    }, e => { },
      () => {
        verificationResultLogger?.Finish();

        var coverageReportDir = options.Get(CommonOptionBag.VerificationCoverageReport);
        if (coverageReportDir != null) {
          new CoverageReporter(options).SerializeVerificationCoverageReport(
            proofDependencyManager, resolution.ResolvedProgram,
            usedDependencies,
            coverageReportDir);
        }
      });
  }

  public void ReportVerificationDiagnostics() {
    VerificationResults.Subscribe(result => {
      // We use an intermediate reporter so we can sort the diagnostics from all parts by token
      var batchReporter = new BatchErrorReporter(options);
      foreach (var completed in result.Results) {
        Compilation.ReportDiagnosticsInResult(options, result.CanVerify.NameToken.val, result.CanVerify.NameToken,
          (uint)completed.Result.RunTime.Seconds,
          completed.Result, batchReporter);
      }

      foreach (var diagnostic in batchReporter.AllMessages.OrderBy(m => m.Token)) {
        Compilation.Reporter.Message(diagnostic.Source, diagnostic.Level, diagnostic.ErrorId, diagnostic.Token,
          diagnostic.Message);
      }
    });
  }

  public void ReportVerificationSummary() {
    var statistics = new VerificationStatistics();

    VerificationResults.Subscribe(result => {
      foreach (var taskResult in result.Results) {
        var runResult = taskResult.Result;

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
    }, () => {
      WriteTrailer(options, options.OutputWriter, verifiedAssertions, statistics);
    });
  }

  public IObservable<CanVerifyResult> VerificationResults => verificationResults;
  private readonly Subject<CanVerifyResult> verificationResults = new();

  public Task VerifyAll() {
    var task = new TaskCompletionSource();
    verificationResults.Subscribe(_ => { }, e =>
      task.TrySetException(e), () =>
      task.TrySetResult());
    VerifyAllLazily().ToObservable().Subscribe(verificationResults);
    return task.Task;
  }

  private async IAsyncEnumerable<CanVerifyResult> VerifyAllLazily() {
    var canVerifyResults = new Dictionary<ICanVerify, CliCanVerifyState>();
    Compilation.Updates.Subscribe(ev => {

      if (ev is CanVerifyPartsIdentified canVerifyPartsIdentified) {
        var canVerifyResult = canVerifyResults[canVerifyPartsIdentified.CanVerify];
        foreach (var part in canVerifyPartsIdentified.Parts.Where(canVerifyResult.TaskFilter)) {
          canVerifyResult.Tasks.Add(part);
        }

        if (canVerifyResult.CompletedParts.Count == canVerifyResult.Tasks.Count) {
          canVerifyResult.Finished.SetResult();
        }
      }

      if (ev is BoogieException boogieException) {
        var canVerifyResult = canVerifyResults[boogieException.CanVerify];
        canVerifyResult.Finished.SetException(boogieException.Exception);
      }

      if (ev is BoogieUpdate boogieUpdate) {
        if (boogieUpdate.BoogieStatus is Completed completed) {
          var canVerifyResult = canVerifyResults[boogieUpdate.CanVerify];
          canVerifyResult.CompletedParts.Add((boogieUpdate.VerificationTask, completed));

          if (canVerifyResult.CompletedParts.Count == canVerifyResult.Tasks.Count) {
            canVerifyResult.Finished.TrySetResult();
          }
        }
      }
    });

    ResolutionResult resolution;
    try {
      resolution = await Compilation.Resolution;
    } catch (OperationCanceledException) {
      // Failed to resolve the program due to a user error.
      yield break;
    }

    if (errorCount > 0) {
      yield break;
    }

    var canVerifies = resolution.CanVerifies?.DistinctBy(v => v.Tok).ToList();

    if (canVerifies == null) {
      yield break;
    }

    canVerifies = FilterCanVerifies(canVerifies, out var line);
    verifiedAssertions = line != null;

    var orderedCanVerifies = canVerifies.OrderBy(v => v.Tok.pos).ToList();
    foreach (var canVerify in orderedCanVerifies) {
      var results = new CliCanVerifyState();
      canVerifyResults[canVerify] = results;
      if (line != null) {
        results.TaskFilter = t => KeepVerificationTask(t, line.Value);
      }

      await Compilation.VerifyCanVerify(canVerify, results.TaskFilter);
    }

    foreach (var canVerify in orderedCanVerifies) {
      var results = canVerifyResults[canVerify];
      try {
        var timeLimitSeconds = TimeSpan.FromSeconds(options.Get(BoogieOptionBag.VerificationTimeLimit));
        var tasks = new List<Task> { results.Finished.Task };
        if (timeLimitSeconds.Seconds != 0) {
          tasks.Add(Task.Delay(timeLimitSeconds));
        }
        await Task.WhenAny(tasks);
        if (!results.Finished.Task.IsCompleted) {
          Compilation.Reporter.Error(MessageSource.Verifier, canVerify.Tok,
            "Dafny encountered an internal error while waiting for this symbol to verify. Please report it at <https://github.com/dafny-lang/dafny/issues>.\n");
          break;
        }
        await results.Finished.Task;
      } catch (ProverException e) {
        Compilation.Reporter.Error(MessageSource.Verifier, ResolutionErrors.ErrorId.none, canVerify.Tok, e.Message);
        throw;
      } catch (Exception e) {
        Compilation.Reporter.Error(MessageSource.Verifier, ResolutionErrors.ErrorId.none, canVerify.Tok,
          $"Internal error occurred during verification: {e.Message}\n{e.StackTrace}");
        throw;
      }
      yield return new CanVerifyResult(canVerify, results.CompletedParts.Select(c => new VerificationTaskResult(c.Task, c.Result.Result)).ToList());

      canVerifyResults.Remove(canVerify); // Free memory
    }
  }

  private List<ICanVerify> FilterCanVerifies(List<ICanVerify> canVerifies, out int? line) {
    var symbolFilter = options.Get(VerifyCommand.FilterSymbol);
    if (symbolFilter != null) {
      canVerifies = canVerifies.Where(canVerify => canVerify.FullDafnyName.Contains(symbolFilter)).ToList();
    }

    var filterPosition = options.Get(VerifyCommand.FilterPosition);
    if (filterPosition == null) {
      line = null;
      return canVerifies;
    }

    var regex = new Regex(@"(.*)(?::(\d+))?", RegexOptions.RightToLeft);
    var result = regex.Match(filterPosition);
    if (result.Length != filterPosition.Length || !result.Success) {
      Compilation.Reporter.Error(MessageSource.Project, Token.Cli, "Could not parse value passed to --filter-position");
      line = null;
      return new List<ICanVerify>();
    }
    var filePart = result.Groups[1].Value;
    string? linePart = result.Groups.Count > 2 ? result.Groups[2].Value : null;
    var fileFiltered = canVerifies.Where(c => c.Tok.Uri.ToString().EndsWith(filePart)).ToList();
    if (string.IsNullOrEmpty(linePart)) {
      line = null;
      return fileFiltered;
    }

    var parsedLine = int.Parse(linePart);
    line = parsedLine;
    return fileFiltered.Where(c =>
        c.RangeToken.StartToken.line <= parsedLine && parsedLine <= c.RangeToken.EndToken.line).ToList();
  }

  private bool KeepVerificationTask(IVerificationTask task, int line) {
    return task.ScopeToken.line == line || task.Token.line == line;
  }

  static void WriteTrailer(DafnyOptions options, TextWriter output, bool reportAssertions, VerificationStatistics statistics) {
    if (options.Verbosity <= CoreOptions.VerbosityLevel.Quiet) {
      return;
    }

    output.WriteLine();

    if (reportAssertions) {
      output.Write("{0} finished with {1} assertions verified, {2} error{3}", options.DescriptiveToolName,
        statistics.VerifiedAssertions, statistics.ErrorCount,
        Util.Plural(statistics.ErrorCount));

    } else {
      output.Write("{0} finished with {1} verified, {2} error{3}", options.DescriptiveToolName,
        statistics.VerifiedSymbols, statistics.ErrorCount,
        Util.Plural(statistics.ErrorCount));
    };
    if (statistics.InconclusiveCount != 0) {
      output.Write(", {0} inconclusive{1}", statistics.InconclusiveCount, Util.Plural(statistics.InconclusiveCount));
    }

    if (statistics.TimeoutCount != 0) {
      output.Write(", {0} time out{1}", statistics.TimeoutCount, Util.Plural(statistics.TimeoutCount));
    }

    if (statistics.OutOfMemoryCount != 0) {
      output.Write(", {0} out of memory", statistics.OutOfMemoryCount);
    }

    if (statistics.OutOfResourceCount != 0) {
      output.Write(", {0} out of resource", statistics.OutOfResourceCount);
    }

    if (statistics.SolverExceptionCount != 0) {
      output.Write(", {0} solver exceptions", statistics.SolverExceptionCount);
    }

    output.WriteLine();
    output.Flush();
  }
}

record VerificationStatistics {
  public int ErrorCount;
  public int VerifiedAssertions;
  public int VerifiedSymbols;
  public int InconclusiveCount;
  public int TimeoutCount;
  public int OutOfResourceCount;
  public int OutOfMemoryCount;
  public int SolverExceptionCount;
}