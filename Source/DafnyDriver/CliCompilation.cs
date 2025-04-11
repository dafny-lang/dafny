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
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using VC;
using VCGeneration;
using Token = Microsoft.Dafny.Token;

namespace DafnyDriver.Commands;

public record CanVerifyResult(ICanVerify CanVerify, IReadOnlyList<VerificationTaskResult> Results);

public class CliCompilation {
  public Compilation Compilation { get; }
  private readonly ConcurrentDictionary<MessageSource, int> errorsPerSource = new();
  private int errorCount;
  private int warningCount;
  public bool DidVerification { get; private set; }

  private CliCompilation(
    CreateCompilation createCompilation,
    DafnyOptions options) {
    Options = options;

    if (options.DafnyProject == null) {
      var firstFile = options.CliRootSourceUris.FirstOrDefault();
      var uri = firstFile ?? new Uri(Directory.GetCurrentDirectory());
      options.DafnyProject = new DafnyProject(null, uri, null, new HashSet<string>() { uri.LocalPath }, new HashSet<string>(),
        new Dictionary<string, object>()) {
        ImplicitFromCli = true
      };
    }

    options.RunningBoogieFromCommandLine = true;

    var input = new CompilationInput(options, 0, options.DafnyProject);
    var executionEngine = new ExecutionEngine(options, new EmptyVerificationResultCache(), DafnyMain.LargeThreadScheduler);
    Compilation = createCompilation(executionEngine, input);
  }

  public async Task<int> GetAndReportExitCode() {
    var value = await GetAndReportExitValue();
    return (int)value;
  }

  public async Task<ExitValue> GetAndReportExitValue() {
    if (errorCount > 0) {
      if (HasErrorsFromSource(MessageSource.Project)) {
        return ExitValue.PREPROCESSING_ERROR;
      }

      if (HasErrorsFromSource(MessageSource.Verifier)) {
        return ExitValue.VERIFICATION_ERROR;
      }
      return ExitValue.DAFNY_ERROR;
    }

    if (warningCount > 0 && !Options.Get(CommonOptionBag.AllowWarnings)) {
      await Options.OutputWriter.WriteLineAsync(
        "Compilation failed because warnings were found and --allow-warnings is false");
      return ExitValue.DAFNY_ERROR;
    }

    return ExitValue.SUCCESS;

    bool HasErrorsFromSource(MessageSource source) {
      return errorsPerSource.GetOrAdd(source, _ => 0) != 0;
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

        if (newDiagnostic.Diagnostic.Level == ErrorLevel.Warning) {
          Interlocked.Increment(ref warningCount);
        }

        consoleReporter.MessageCore(newDiagnostic.Diagnostic);
      } else if (ev is FinishedParsing finishedParsing) {
        if (errorCount > 0) {
          var programName = finishedParsing.ParseResult.Program.Name;
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

  public async IAsyncEnumerable<CanVerifyResult> VerifyAllLazily(int? randomSeed = null) {
    if (!Options.Get(CommonOptionBag.UnicodeCharacters) && Options.Backend is not CppBackend) {
      Compilation.Reporter.Deprecated(MessageSource.Verifier, "unicodeCharDeprecated", Token.Cli,
        "the option unicode-char has been deprecated.");
    }

    var canVerifyResults = new Dictionary<ICanVerify, CliCanVerifyState>();
    using var subscription = Compilation.Updates.Subscribe(ev => {

      if (ev is CanVerifyPartsIdentified canVerifyPartsIdentified) {
        var canVerifyResult = canVerifyResults[canVerifyPartsIdentified.CanVerify];
        foreach (var part in canVerifyPartsIdentified.Parts.Where(canVerifyResult.TaskFilter)) {
          Interlocked.Increment(ref canVerifyResult.TaskCount);
        }

        if (canVerifyResult.CompletedParts.Count == canVerifyResult.TaskCount) {
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
        var completedPartsCount = Interlocked.Increment(ref canVerifyResult.CompletedCount);

        if (Options.Get(CommonOptionBag.ProgressOption) == CommonOptionBag.ProgressLevel.Batch) {
          var partOrigin = boogieUpdate.VerificationTask.Split.Token;

          var wellFormedness = boogieUpdate.VerificationTask.Split.Implementation.Name.Contains("CheckWellFormed$");

          string OriginDescription(IImplementationPartOrigin origin, bool outer) {
            if (outer && origin is ImplementationRootOrigin) {
              return (wellFormedness ? "contract consistency" : "entire body");
            }
            var result = origin switch {
              PathOrigin pathOrigin => $"{OriginDescription(pathOrigin.Inner, false)}" +
                                       $"after executing lines {string.Join(", ", pathOrigin.BranchTokens.Select(b => b.line))}",
              RemainingAssertionsOrigin remainingAssertions => OriginDescription(remainingAssertions.Origin, false) + (outer ? "remaining assertions" : ""),
              IsolatedAssertionOrigin isolateOrigin => $"{OriginDescription(isolateOrigin.Origin, false)}assertion at line {isolateOrigin.line}",
              JumpOrigin returnOrigin => $"{OriginDescription(returnOrigin.Origin, false)}{JumpOriginKind(returnOrigin)} at line {returnOrigin.line}",
              AfterSplitOrigin splitOrigin => $"{OriginDescription(splitOrigin.Inner, false)}assertions after split_here at line {splitOrigin.line}",
              FocusOrigin focusOrigin =>
                $"{OriginDescription(focusOrigin.Inner, false)}with focus " +
                $"{string.Join(", ", focusOrigin.FocusChoices.Select(b => (b.DidFocus ? "+" : "-") + b.Token.line))}",
              UntilFirstSplitOrigin untilFirstSplit => $"{OriginDescription(untilFirstSplit.Inner, false)}assertions until first split",
              ImplementationRootOrigin => "",
              _ => throw new ArgumentOutOfRangeException(nameof(origin), origin, null)
            };
            if (!outer && !string.IsNullOrEmpty(result)) {
              result += ", ";
            }
            return result;
          }

          var runResult = completed.Result;
          var timeString = runResult.RunTime.ToString("g");
          Options.OutputWriter.WriteLine(
            $"Verified {completedPartsCount}/{canVerifyResult.TaskCount} of {boogieUpdate.CanVerify.FullDafnyName}: " +
            $"{OriginDescription(partOrigin, true)} - " +
            $"{DescribeOutcome(Compilation.GetOutcome(runResult.Outcome))}" +
            $" (time: {timeString}, resource count: {runResult.ResourceCount})");
        }
        if (completedPartsCount == canVerifyResult.TaskCount) {
          canVerifyResult.Finished.TrySetResult();
        }
      }
    });

    var resolution = await Compilation.Resolution;
    if (resolution == null || resolution.HasErrors) {
      yield break;
    }

    var canVerifies = resolution.CanVerifies?.ToList();

    if (canVerifies == null) {
      yield break;
    }

    DidVerification = true;

    canVerifies = FilterCanVerifies(canVerifies, out var filterRange);
    VerifiedAssertions = filterRange.Filters;

    int done = 0;

    var canVerifiesPerModule = canVerifies.GroupBy(c => c.ContainingModule);
    foreach (var canVerifiesForModule in canVerifiesPerModule.
               OrderBy(v => v.Key.Origin.pos)) {
      var toAwait = new List<ICanVerify>();
      foreach (var canVerify in canVerifiesForModule.OrderBy(v => v.Origin.pos)) {
        var results = new CliCanVerifyState();
        canVerifyResults[canVerify] = results;
        if (VerifiedAssertions) {
          results.TaskFilter = t => KeepVerificationTask(t, filterRange);
        }

        var shouldVerify = await Compilation.VerifyLocation(canVerify.Origin.GetFilePosition(), results.TaskFilter, randomSeed);
        if (shouldVerify) {
          toAwait.Add(canVerify);
        }
      }

      foreach (var canVerify in toAwait) {
        var results = canVerifyResults[canVerify];
        try {
          if (Options.Get(CommonOptionBag.ProgressOption) > CommonOptionBag.ProgressLevel.None) {
            await Options.OutputWriter.WriteLineAsync(
              $"Verified {done}/{canVerifies.ToList().Count} symbols. Waiting for {canVerify.FullDafnyName} to verify.");
          }

          await results.Finished.Task;
          done++;
        } catch (ProverException e) {
          Compilation.Reporter.Error(MessageSource.Verifier, ResolutionErrors.ErrorId.none, canVerify.Origin, e.Message);
          yield break;
        } catch (OperationCanceledException) {

        } catch (Exception e) {
          Compilation.Reporter.Error(MessageSource.Verifier, ResolutionErrors.ErrorId.none, canVerify.Origin,
            $"Internal error occurred during verification: {e.Message}\n{e.StackTrace}");
          throw;
        }

        yield return new CanVerifyResult(canVerify,
          results.CompletedParts.Select(c => new VerificationTaskResult(c.Task, c.Result.Result)).ToList());

        canVerifyResults.Remove(canVerify); // Free memory
        Compilation.ClearCanVerifyCache(canVerify);
      }
      Compilation.ClearModuleCache(canVerifiesForModule.Key);
    }
  }

  private static string JumpOriginKind(JumpOrigin returnOrigin) {
    return returnOrigin.IsolatedReturn is GotoCmd ? "continue" : "return";
  }

  public static string DescribeOutcome(VcOutcome outcome) {
    return outcome switch {
      VcOutcome.Correct => "verified successfully",
      VcOutcome.Errors => "could not be verified",
      VcOutcome.Inconclusive => "was inconclusive",
      VcOutcome.TimedOut => "timed out",
      VcOutcome.OutOfResource => "ran out of resources",
      VcOutcome.OutOfMemory => "ran out of memory",
      VcOutcome.SolverException => "ran into a solver exception",
      _ => throw new ArgumentOutOfRangeException(nameof(outcome), outcome, null)
    };
  }

  class LineRange(int start, int end) {
    public int Start { get; } = start;
    public int End { get; } = end;

    public bool Contains(int value) {
      return Start <= value && value <= End;
    }
    public bool Filters => Start != int.MinValue || End != int.MaxValue;
  }

  private List<ICanVerify> FilterCanVerifies(List<ICanVerify> canVerifies, out LineRange range) {
    var symbolFilter = Options.Get(VerifyCommand.FilterSymbol);
    int start = int.MinValue;
    int end = int.MaxValue;
    if (symbolFilter != null) {
      if (symbolFilter.EndsWith(".")) {
        var withoutDot = new string(symbolFilter.SkipLast(1).ToArray());
        canVerifies = canVerifies.Where(canVerify => canVerify.FullDafnyName.EndsWith(withoutDot)).ToList();
      } else {
        canVerifies = canVerifies.Where(canVerify => canVerify.FullDafnyName.Contains(symbolFilter)).ToList();
      }
    }

    var filterPosition = Options.Get(VerifyCommand.FilterPosition);
    if (filterPosition == null) {
      range = new LineRange(start, end);
      return canVerifies;
    }

    var regex = new Regex(@"(.*)(?::(\d*)(-?)(\d*))?", RegexOptions.RightToLeft);
    var result = regex.Match(filterPosition);
    if (result.Length != filterPosition.Length || !result.Success) {
      Compilation.Reporter.Error(MessageSource.Project, Token.Cli, "Could not parse value passed to --filter-position");
      range = new LineRange(start, end);
      return [];
    }
    var filePart = result.Groups[1].Value;
    string? lineStart = result.Groups[2].Value;
    bool hasRange = result.Groups[3].Value == "-";
    string lineEnd = result.Groups[4].Value;
    var fileFiltered = canVerifies.Where(c => c.Origin.Uri.ToString().EndsWith(filePart)).ToList();
    if (string.IsNullOrEmpty(lineStart) && string.IsNullOrEmpty(lineEnd)) {
      range = new LineRange(start, end);
      return fileFiltered;
    }

    if (!string.IsNullOrEmpty(lineEnd)) {
      end = int.Parse(lineEnd);
      if (!hasRange) {
        start = end;
      }
    }
    if (!string.IsNullOrEmpty(lineStart)) {
      start = int.Parse(lineStart);
    }

    range = new LineRange(start, end);
    return fileFiltered.Where(c =>
        c.StartToken.line <= end && start <= c.EndToken.line).ToList();
  }

  private bool KeepVerificationTask(IVerificationTask task, LineRange range) {
    return range.Contains(task.ScopeToken.line) || range.Contains(task.Token.line);
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
  public int TotalResourcesUsed;
  public int MaxVcResourcesUsed;
}
