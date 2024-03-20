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
using Microsoft.Extensions.Logging;
using Token = Microsoft.Dafny.Token;

namespace DafnyDriver.Commands;

public record CanVerifyResult(ICanVerify CanVerify, IReadOnlyList<VerificationTaskResult> Results);

public class CliCompilation {
  public Compilation Compilation { get; }
  private readonly ConcurrentDictionary<MessageSource, int> errorsPerSource = new();
  private int errorCount;
  public bool DidVerification { get; private set; }

  private CliCompilation(
    CreateCompilation createCompilation,
    DafnyOptions options) {
    Options = options;

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

  public Task<ResolutionResult?> Resolution => Compilation.Resolution;

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

  public void Start() {
    if (Compilation.Started) {
      throw new InvalidOperationException("Compilation was already started");
    }

    ErrorReporter consoleReporter = Options.DiagnosticsFormat switch {
      DafnyOptions.DiagnosticsFormats.PlainText => new ConsoleErrorReporter(Options),
      DafnyOptions.DiagnosticsFormats.JSON => new JsonConsoleErrorReporter(Options),
      _ => throw new ArgumentOutOfRangeException()
    };

    var internalExceptionsFound = 0;
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
          Options.OutputWriter.WriteLine($"{errorCount} parse errors detected in {programName}");
        }
      } else if (ev is FinishedResolution finishedResolution) {
        DafnyMain.MaybePrintProgram(finishedResolution.Result.ResolvedProgram, Options.DafnyPrintResolvedFile, true);

        if (errorCount > 0) {
          var programName = finishedResolution.Result.ResolvedProgram.Name;
          Options.OutputWriter.WriteLine($"{errorCount} resolution/type errors detected in {programName}");
        }
      } else if (ev is InternalCompilationException internalCompilationException) {
        if (Interlocked.Increment(ref internalExceptionsFound) == 1) {
          Options.OutputWriter.WriteLine($"Encountered internal compilation exception: {internalCompilationException.Exception.Message}");
        }
      }

    });
    Compilation.Start();
  }

  public DafnyOptions Options { get; }

  public bool VerifiedAssertions { get; private set; }

  public async IAsyncEnumerable<CanVerifyResult> VerifyAllLazily(int? randomSeed) {
    var canVerifyResults = new Dictionary<ICanVerify, CliCanVerifyState>();
    using var subscription = Compilation.Updates.Subscribe(ev => {

      if (ev is CanVerifyPartsIdentified canVerifyPartsIdentified) {
        var canVerifyResult = canVerifyResults[canVerifyPartsIdentified.CanVerify];
        foreach (var part in canVerifyPartsIdentified.Parts.Where(canVerifyResult.TaskFilter)) {
          canVerifyResult.Tasks.Add(part);
        }

        if (canVerifyResult.CompletedParts.Count == canVerifyResult.Tasks.Count) {
          canVerifyResult.Finished.SetResult();
        }
      }
      if (ev is InternalCompilationException internalCompilationException) {
        foreach (var state in canVerifyResults.Values) {
          state.Finished.TrySetException(internalCompilationException.Exception);
        }
      }

      if (ev is BoogieException boogieException) {
        var canVerifyResult = canVerifyResults[boogieException.CanVerify];
        canVerifyResult.Finished.SetException(boogieException.Exception);
      }

      if (ev is BoogieUpdate { BoogieStatus: Completed completed } boogieUpdate) {
        var canVerifyResult = canVerifyResults[boogieUpdate.CanVerify];
        canVerifyResult.CompletedParts.Enqueue((boogieUpdate.VerificationTask, completed));

        if (canVerifyResult.CompletedParts.Count == canVerifyResult.Tasks.Count) {
          canVerifyResult.Finished.TrySetResult();
        }
      }
    });

    var resolution = await Compilation.Resolution;
    if (resolution == null || resolution.HasErrors) {
      yield break;
    }

    var canVerifies = resolution.CanVerifies?.DistinctBy(v => v.Tok).ToList();

    if (canVerifies == null) {
      yield break;
    }

    DidVerification = true;

    canVerifies = FilterCanVerifies(canVerifies, out var line);
    VerifiedAssertions = line != null;

    var orderedCanVerifies = canVerifies.OrderBy(v => v.Tok.pos).ToList();
    foreach (var canVerify in orderedCanVerifies) {
      var results = new CliCanVerifyState();
      canVerifyResults[canVerify] = results;
      if (line != null) {
        results.TaskFilter = t => KeepVerificationTask(t, line.Value);
      }

      var shouldVerify = await Compilation.VerifyCanVerify(canVerify, results.TaskFilter, randomSeed);
      if (!shouldVerify) {
        orderedCanVerifies.Remove(canVerify);
      }
    }

    foreach (var canVerify in orderedCanVerifies) {
      var results = canVerifyResults[canVerify];
      try {
        var timeLimitSeconds = TimeSpan.FromSeconds(Options.Get(BoogieOptionBag.VerificationTimeLimit));
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
        yield break;
      } catch (OperationCanceledException) {

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
    var symbolFilter = Options.Get(VerifyCommand.FilterSymbol);
    if (symbolFilter != null) {
      canVerifies = canVerifies.Where(canVerify => canVerify.FullDafnyName.Contains(symbolFilter)).ToList();
    }

    var filterPosition = Options.Get(VerifyCommand.FilterPosition);
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