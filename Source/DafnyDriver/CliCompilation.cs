#nullable enable
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.FileSystemGlobbing;
using Microsoft.Extensions.Logging;
using VC;
using IToken = Microsoft.Dafny.IToken;
using Token = Microsoft.Dafny.Token;

namespace DafnyDriver.Commands;

public class CliCompilation {
  private readonly DafnyOptions options;

  private Compilation Compilation { get; }
  private readonly ConcurrentDictionary<MessageSource, int> errorsPerSource = new();
  private int errorCount;

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

  public async Task VerifyAllAndPrintSummary() {
    var statSum = new PipelineStatistics();

    var canVerifyResults = new Dictionary<ICanVerify, CliCanVerifyResults>();
    Compilation.Updates.Subscribe(ev => {

      if (ev is CanVerifyPartsIdentified canVerifyPartsIdentified) {
        var canVerifyResult = canVerifyResults[canVerifyPartsIdentified.CanVerify];
        foreach (var part in canVerifyPartsIdentified.Parts) {
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
          canVerifyResult.CompletedParts.Add((boogieUpdate.ImplementationTask, completed));

          switch (completed.Result.Outcome) {
            case ConditionGeneration.Outcome.Correct:
            case ConditionGeneration.Outcome.ReachedBound:
              Interlocked.Increment(ref statSum.VerifiedCount);
              break;
            case ConditionGeneration.Outcome.Errors:
              Interlocked.Add(ref statSum.ErrorCount, completed.Result.Errors.Count);
              break;
            case ConditionGeneration.Outcome.TimedOut:
              Interlocked.Increment(ref statSum.TimeoutCount);
              break;
            case ConditionGeneration.Outcome.OutOfMemory:
              Interlocked.Increment(ref statSum.OutOfMemoryCount);
              break;
            case ConditionGeneration.Outcome.OutOfResource:
              Interlocked.Increment(ref statSum.OutOfResourceCount);
              break;
            case ConditionGeneration.Outcome.Inconclusive:
              Interlocked.Increment(ref statSum.InconclusiveCount);
              break;
            default:
              throw new ArgumentOutOfRangeException();
          }

          if (canVerifyResult.CompletedParts.Count == canVerifyResult.Tasks.Count) {
            canVerifyResult.Finished.TrySetResult();
          }
        }
      }
    });

    try {
      var resolution = await Compilation.Resolution;
      if (errorCount > 0) {
        return;
      }

      var canVerifies = resolution.CanVerifies?.DistinctBy(v => v.Tok).ToList();

      if (canVerifies != null) {
        canVerifies = FilterCanVerifies(canVerifies);

        var orderedCanVerifies = canVerifies.OrderBy(v => v.Tok.pos).ToList();
        foreach (var canVerify in orderedCanVerifies) {
          canVerifyResults[canVerify] = new CliCanVerifyResults();
          await Compilation.VerifyCanVerify(canVerify, false);
        }

        foreach (var canVerify in orderedCanVerifies) {
          var results = canVerifyResults[canVerify];
          try {
            await results.Finished.Task;
            foreach (var (task, completed) in results.CompletedParts.OrderBy(t => t.Item1.Implementation.Name)) {
              foreach (var vcResult in completed.Result.VCResults) {
                Compilation.ReportDiagnosticsInResult(options, task, vcResult, Compilation.Reporter);
              }

              ProofDependencyWarnings.WarnAboutSuspiciousDependenciesForImplementation(options,
                resolution.ResolvedProgram!.Reporter,
                resolution.ResolvedProgram.ProofDependencyManager,
                new DafnyConsolePrinter.ImplementationLogEntry(task.Implementation.VerboseName,
                  task.Implementation.tok),
                DafnyConsolePrinter.DistillVerificationResult(completed.Result));
            }
          } catch (ProverException e) {
            Interlocked.Increment(ref statSum.SolverExceptionCount);
            Compilation.Reporter.Error(MessageSource.Verifier, ResolutionErrors.ErrorId.none, canVerify.Tok, e.Message);
          } catch (Exception e) {
            Interlocked.Increment(ref statSum.SolverExceptionCount);
            Compilation.Reporter.Error(MessageSource.Verifier, ResolutionErrors.ErrorId.none, canVerify.Tok,
              $"Internal error occurred during verification: {e.Message}\n{e.StackTrace}");
          }
        }
      }

      SynchronousCliCompilation.WriteTrailer(options, /* TODO ErrorWriter? */ options.OutputWriter, statSum);

    } catch (OperationCanceledException) {
      // Failed to resolve the program due to a user error.
    }
  }

  private List<ICanVerify> FilterCanVerifies(List<ICanVerify> canVerifies) {
    var filterPosition = options.Get(VerifyCommand.FilterPosition);
    if (filterPosition == null) {
      return canVerifies;
    }

    var regex = new Regex(@"(.+)(?::(\d+))?", RegexOptions.RightToLeft);
    var result = regex.Match(filterPosition);
    if (result.Length != filterPosition.Length || !result.Success) {
      Compilation.Reporter.Error(MessageSource.Project, Token.Cli, "Could not parse value passed to --filter-position");
      return new List<ICanVerify>();
    }
    var filePart = result.Groups[1].Value;
    string? linePart = result.Groups.Count > 2 ? result.Groups[2].Value : null;
    var fileFiltered = canVerifies.Where(c => c.Tok.Uri.ToString().EndsWith(filePart)).ToList();
    if (string.IsNullOrEmpty(linePart)) {
      return fileFiltered;
    }

    var line = int.Parse(linePart);
    return fileFiltered.Where(c =>
        c.RangeToken.StartToken.line <= line && line <= c.RangeToken.EndToken.line).ToList();
  }
}