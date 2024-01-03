using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;

namespace DafnyDriver.Commands;

public class CliCompilation {
  private readonly DafnyOptions options;

  private readonly CreateCompilation createCompilation;
  public Compilation Compilation { get; private set; }
  private readonly ConcurrentDictionary<MessageSource, int> errorsPerSource = new();
  private int errorCount;

  public CliCompilation(
    CreateCompilation createCompilation,
    DafnyOptions options) {
    this.options = options;
    this.createCompilation = createCompilation;
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
    var resolution = await Compilation.Resolution;
    if (errorCount > 0) {
      return;
    }

    var statSum = new PipelineStatistics();
    var canVerifyResults = new Dictionary<FilePosition, CliCanVerifyResults>();
    Compilation.Updates.Subscribe(ev => {

      if (ev is CanVerifyPartsIdentified canVerifyPartsIdentified) {
        var canVerifyResult = canVerifyResults[canVerifyPartsIdentified.CanVerify.Tok.GetFilePosition()];
        foreach (var part in canVerifyPartsIdentified.Parts) {
          canVerifyResult.Tasks.Add(part);
        }
        if (canVerifyResult.CompletedParts.Count == canVerifyResult.Tasks.Count) {
          canVerifyResult.Finished.SetResult();
        }
      }

      if (ev is BoogieUpdate boogieUpdate) {
        if (boogieUpdate.BoogieStatus is Completed completed) {
          var dafnyToken = BoogieGenerator.ToDafnyToken(false, boogieUpdate.ImplementationTask.Implementation.tok);
          var canVerifyResult = canVerifyResults[dafnyToken.GetFilePosition()];
          canVerifyResult.CompletedParts.Add((boogieUpdate.ImplementationTask, completed));
          if (canVerifyResult.CompletedParts.Count == canVerifyResult.Tasks.Count) {
            canVerifyResult.Finished.SetResult();
          }
        }
        if (boogieUpdate.BoogieStatus is BatchCompleted batchCompleted) {
          switch (batchCompleted.VcResult.outcome) {
            case ProverInterface.Outcome.Valid:
            case ProverInterface.Outcome.Bounded:
              Interlocked.Increment(ref statSum.VerifiedCount);
              break;
            case ProverInterface.Outcome.Invalid:
              Interlocked.Add(ref statSum.ErrorCount, batchCompleted.VcResult.counterExamples.Count);
              break;
            case ProverInterface.Outcome.TimeOut:
              Interlocked.Increment(ref statSum.TimeoutCount);
              break;
            case ProverInterface.Outcome.OutOfMemory:
              Interlocked.Increment(ref statSum.OutOfMemoryCount);
              break;
            case ProverInterface.Outcome.OutOfResource:
              Interlocked.Increment(ref statSum.OutOfResourceCount);
              break;
            case ProverInterface.Outcome.Undetermined:
              Interlocked.Increment(ref statSum.InconclusiveCount);
              break;
            default:
              throw new ArgumentOutOfRangeException();
          }
        }
      }
    });

    var canVerifies = resolution.CanVerifies?.ToList();

    if (canVerifies != null) {
      var orderedCanVerifies = canVerifies.OrderBy(v => v.Tok.pos).ToList();
      foreach (var canVerify in orderedCanVerifies) {
        canVerifyResults[canVerify.Tok.GetFilePosition()] = new CliCanVerifyResults();
        await Compilation.VerifyCanVerify(canVerify, false);
      }

      foreach (var canVerify in orderedCanVerifies) {
        var results = canVerifyResults[canVerify.Tok.GetFilePosition()];
        await results.Finished.Task;
        foreach (var (task, completed) in results.CompletedParts.
                   OrderBy(t => t.Item1.Implementation.Name)) {
          foreach (var vcResult in completed.Result.VCResults) {
            Compilation.ReportDiagnosticsInResult(options, task, vcResult, Compilation.Reporter);
          }
        }
      }
    }
    LegacyCliCompilation.WriteTrailer(options, /* TODO ErrorWriter? */ options.OutputWriter, statSum);
  }
}