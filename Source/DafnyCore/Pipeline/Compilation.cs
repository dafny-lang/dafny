#nullable enable

using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Reactive;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.Compilers;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using VC;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny;

public delegate Compilation CreateCompilation(
  ExecutionEngine boogieEngine,
  CompilationInput compilation);

public record FilePosition(Uri Uri, Position Position);
/// <summary>
/// The compilation of a single version of a program
/// After calling Start, the document will be parsed and resolved.
///
/// To verify a symbol, VerifySymbol must be called.
/// </summary>
public class Compilation : IDisposable {

  private readonly ILogger logger;
  private readonly IFileSystem fileSystem;
  private readonly ITextDocumentLoader documentLoader;
  private readonly IProgramVerifier verifier;

  private readonly TaskCompletionSource started = new();
  private readonly CancellationTokenSource cancellationSource;

  public bool Started => started.Task.IsCompleted;

  private readonly ConcurrentDictionary<Uri, ConcurrentStack<DafnyDiagnostic>> staticDiagnostics = new();
  public DafnyDiagnostic[] GetDiagnosticsForUri(Uri uri) =>
    staticDiagnostics.TryGetValue(uri, out var forUri) ? forUri.ToArray() : Array.Empty<DafnyDiagnostic>();

  /// <summary>
  /// FilePosition is required because the default module lives in multiple files
  /// </summary>
  private readonly LazyConcurrentDictionary<ModuleDefinition,
    Task<IReadOnlyDictionary<FilePosition, IReadOnlyList<IVerificationTask>>>> translatedModules = new();

  private readonly ConcurrentDictionary<ICanVerify, Unit> verifyingOrVerifiedSymbols = new();
  private readonly LazyConcurrentDictionary<ICanVerify, IReadOnlyList<IVerificationTask>> tasksPerVerifiable = new();

  private DafnyOptions Options => Input.Options;
  public CompilationInput Input { get; }
  public DafnyProject Project => Input.Project;
  private readonly ExecutionEngine boogieEngine;

  private readonly Subject<ICompilationEvent> updates = new();
  public IObservable<ICompilationEvent> Updates => updates;

  private Program? programAfterParsing;
  private Program? transformedProgram;
  private readonly IDisposable staticDiagnosticsSubscription;

  private bool disposed;
  private readonly ObservableErrorReporter errorReporter;

  public Task<Program> ParsedProgram { get; }
  public Task<ResolutionResult> Resolution { get; }

  public ErrorReporter Reporter => errorReporter;

  public IReadOnlyList<DafnyFile>? RootFiles { get; set; }
  public bool HasErrors { get; private set; }

  public Compilation(
    ILogger<Compilation> logger,
    IFileSystem fileSystem,
    ITextDocumentLoader documentLoader,
    IProgramVerifier verifier,
    ExecutionEngine boogieEngine,
    CompilationInput input
    ) {
    Input = input;
    this.boogieEngine = boogieEngine;

    this.documentLoader = documentLoader;
    this.logger = logger;
    this.fileSystem = fileSystem;
    this.verifier = verifier;

    errorReporter = new ObservableErrorReporter(Options, Project.Uri);
    errorReporter.Updates.Subscribe(updates);
    staticDiagnosticsSubscription = errorReporter.Updates.Subscribe(newDiagnostic => {
      if (newDiagnostic.Diagnostic.Level == ErrorLevel.Error) {
        HasErrors = true;
      }
      staticDiagnostics.GetOrAdd(newDiagnostic.Uri, _ => new()).Push(newDiagnostic.Diagnostic);
    });

    cancellationSource = new();
    cancellationSource.Token.Register(() => started.TrySetCanceled(cancellationSource.Token));

    verificationTickets.Enqueue(Unit.Default);

    ParsedProgram = ParseAsync();
    Resolution = ResolveAsync();
  }

  public void Start() {
    if (Started) {
      throw new InvalidOperationException("Compilation was already started");
    }

    Project.Errors.CopyDiagnostics(errorReporter);
    RootFiles = DetermineRootFiles();
    updates.OnNext(new DeterminedRootFiles(Project, RootFiles!, GetDiagnosticsCopy()));
    started.TrySetResult();
  }

  private ImmutableDictionary<Uri, ImmutableList<Diagnostic>> GetDiagnosticsCopy() {
    return staticDiagnostics.ToImmutableDictionary(k => k.Key,
      kv => kv.Value.Select(d => d.ToLspDiagnostic()).ToImmutableList());
  }

  private IReadOnlyList<DafnyFile> DetermineRootFiles() {
    var result = new List<DafnyFile>();

    foreach (var uri in Input.Project.GetRootSourceUris(fileSystem)) {
      var file = DafnyFile.CreateAndValidate(errorReporter, fileSystem, Options, uri, Project.StartingToken);
      if (file != null) {
        result.Add(file);
      }
    }

    foreach (var uri in Options.CliRootSourceUris) {
      var shortPath = Path.GetRelativePath(Directory.GetCurrentDirectory(), uri.LocalPath);
      var file = DafnyFile.CreateAndValidate(errorReporter, fileSystem, Options, uri, Token.Cli,
        $"command-line argument '{shortPath}' is neither a recognized option nor a Dafny input file (.dfy, .doo, or .toml).");
      if (file != null) {
        result.Add(file);
      } else {
        return result;
      }
    }
    if (Options.UseStdin) {
      var uri = new Uri("stdin:///");
      result.Add(DafnyFile.CreateAndValidate(errorReporter, fileSystem, Options, uri, Token.Cli));
    }

    if (Options.Get(CommonOptionBag.UseStandardLibraries)) {
      if (Options.CompilerName is null or "cs" or "java" or "go" or "py" or "js") {
        var targetName = Options.CompilerName ?? "notarget";
        var stdlibDooUri = DafnyMain.StandardLibrariesDooUriTarget[targetName];
        result.Add(DafnyFile.CreateAndValidate(errorReporter, OnDiskFileSystem.Instance, Options, stdlibDooUri, Project.StartingToken));
      }

      result.Add(DafnyFile.CreateAndValidate(errorReporter, fileSystem, Options, DafnyMain.StandardLibrariesDooUri, Project.StartingToken));
    }

    var libraryFiles = CommonOptionBag.SplitOptionValueIntoFiles(Options.Get(CommonOptionBag.Libraries).Select(f => f.FullName));
    foreach (var library in libraryFiles) {
      var file = DafnyFile.CreateAndValidate(errorReporter, fileSystem, Options, new Uri(library), Project.StartingToken);
      if (file != null) {
        file.IsPreverified = true;
        file.IsPrecompiled = true;
        result.Add(file);
      }
    }

    var projectPath = Project.Uri.LocalPath;
    if (projectPath.EndsWith(DafnyProject.FileName)) {
      var projectDirectory = Path.GetDirectoryName(projectPath)!;
      var filesMessage = string.Join("\n", result.Select(uri => Path.GetRelativePath(projectDirectory, uri.Uri.LocalPath)));
      if (filesMessage.Any()) {
        errorReporter.Info(MessageSource.Project, Project.StartingToken, "Files referenced by project are:" + Environment.NewLine + filesMessage);
      }
    }

    if (!HasErrors && !result.Any()) {
      errorReporter.Error(MessageSource.Project, CompilerErrors.ErrorId.None, Project.StartingToken,
        "no Dafny source files were specified as input");
    }

    // Allow specifying the same file twice on the CLI
    return result.DistinctBy(d => d.Uri).ToList();
  }

  private async Task<Program> ParseAsync() {
    try {
      await started.Task;
      if (HasErrors) {
        throw new OperationCanceledException();
      }

      transformedProgram = await documentLoader.ParseAsync(this, cancellationSource.Token);
      transformedProgram.HasParseErrors = HasErrors;

      var cloner = new Cloner(true, false);
      programAfterParsing = new Program(cloner, transformedProgram);

      updates.OnNext(new FinishedParsing(programAfterParsing, GetDiagnosticsCopy()));
      logger.LogDebug(
        $"Passed parsedCompilation to documentUpdates.OnNext, resolving ParsedCompilation task for version {Input.Version}.");
      return programAfterParsing;

    } catch (OperationCanceledException) {
      throw;
    } catch (Exception e) {
      updates.OnNext(new InternalCompilationException(e));
      throw;
    }
  }

  private async Task<ResolutionResult> ResolveAsync() {
    try {
      await ParsedProgram;
      var resolution = await documentLoader.ResolveAsync(this, transformedProgram!, cancellationSource.Token);

      updates.OnNext(new FinishedResolution(
        resolution,
        GetDiagnosticsCopy()));
      staticDiagnosticsSubscription.Dispose();
      logger.LogDebug($"Passed resolvedCompilation to documentUpdates.OnNext, resolving ResolvedCompilation task for version {Input.Version}.");
      return resolution;

    } catch (OperationCanceledException) {
      throw;
    } catch (Exception e) {
      updates.OnNext(new InternalCompilationException(e));
      throw;
    }
  }

  public static string GetTaskName(IVerificationTask task) {
    var prefix = task.ScopeId + task.Split.SplitIndex;

    // Refining declarations get the token of what they're refining, so to distinguish them we need to
    // add the refining module name to the prefix.
    if (task.ScopeToken is RefinementToken refinementToken) {
      prefix += "." + refinementToken.InheritingModule.Name;
    }

    return prefix;
  }

  private int runningVerificationJobs;

  // When verifying a symbol, a ticket must be acquired before the SMT part of verification may start.
  private readonly AsyncQueue<Unit> verificationTickets = new();
  public async Task<bool> VerifyLocation(FilePosition verifiableLocation, bool onlyPrepareVerificationForGutterTests = false) {
    cancellationSource.Token.ThrowIfCancellationRequested();

    var resolution = await Resolution;
    if (resolution.HasErrors) {
      throw new TaskCanceledException();
    }

    var canVerify = resolution.ResolvedProgram.FindNode(verifiableLocation.Uri, verifiableLocation.Position.ToDafnyPosition(),
      node => {
        if (node is not ICanVerify) {
          return false;
        }
        // Sometimes traversing the AST can return different versions of a single source AST node,
        // for example in the case of a LeastLemma, which is later also represented as a PrefixLemma.
        // This check ensures that we consistently use the same version of an AST node. 
        return resolution.CanVerifies!.Contains(node);
      }) as ICanVerify;

    if (canVerify == null) {
      return false;
    }

    return await VerifyCanVerify(canVerify, _ => true, onlyPrepareVerificationForGutterTests);
  }

  public async Task<bool> VerifyCanVerify(ICanVerify canVerify, Func<IVerificationTask, bool> taskFilter,
    bool onlyPrepareVerificationForGutterTests = false) {
    var resolution = await Resolution;
    var containingModule = canVerify.ContainingModule;
    if (!containingModule.ShouldVerify(resolution.ResolvedProgram.Compilation)) {
      return false;
    }

    if (!onlyPrepareVerificationForGutterTests && !verifyingOrVerifiedSymbols.TryAdd(canVerify, Unit.Default)) {
      return false;
    }

    updates.OnNext(new ScheduledVerification(canVerify));

    if (onlyPrepareVerificationForGutterTests) {
      await VerifyUnverifiedSymbol(onlyPrepareVerificationForGutterTests, canVerify, resolution, taskFilter);
      return true;
    }

    _ = VerifyUnverifiedSymbol(onlyPrepareVerificationForGutterTests, canVerify, resolution, taskFilter);
    return true;
  }

  private async Task VerifyUnverifiedSymbol(bool onlyPrepareVerificationForGutterTests, ICanVerify canVerify,
    ResolutionResult resolution, Func<IVerificationTask, bool> taskFilter) {
    try {

      var ticket = verificationTickets.Dequeue(CancellationToken.None);
      var containingModule = canVerify.ContainingModule;

      IReadOnlyDictionary<FilePosition, IReadOnlyList<IVerificationTask>> tasksForModule;
      try {
        tasksForModule = await translatedModules.GetOrAdd(containingModule, async () => {
          var result = await verifier.GetVerificationTasksAsync(boogieEngine, resolution, containingModule,
            cancellationSource.Token);
          foreach (var task in result) {
            cancellationSource.Token.Register(task.Cancel);
          }

          return result.GroupBy(t => ((IToken)t.ScopeToken).GetFilePosition()).ToDictionary(
            g => g.Key,
            g => (IReadOnlyList<IVerificationTask>)g.ToList());
        });
      } catch (OperationCanceledException) {
        throw;
      } catch (Exception e) {
        updates.OnNext(new InternalCompilationException(e));
        throw;
      }

      // For updated to be reliable, tasksPerVerifiable must be Lazy
      var updated = false;
      var tasks = tasksPerVerifiable.GetOrAdd(canVerify, () => {
        var result =
          tasksForModule.GetValueOrDefault(canVerify.NameToken.GetFilePosition()) ??
          new List<IVerificationTask>(0);

        updated = true;
        return result;
      });
      if (updated) {
        updates.OnNext(new CanVerifyPartsIdentified(canVerify,
          tasksPerVerifiable[canVerify].ToList()));
      }

      // When multiple calls to VerifyUnverifiedSymbol are made, the order in which they pass this await matches the call order.
      await ticket;

      if (!onlyPrepareVerificationForGutterTests) {
        foreach (var task in tasks.Where(taskFilter)) {
          VerifyTask(canVerify, task);
        }
      }

    }
    finally {
      verificationTickets.Enqueue(Unit.Default);
    }
  }

  private void VerifyTask(ICanVerify canVerify, IVerificationTask task) {
    var statusUpdates = task.TryRun();
    if (statusUpdates == null) {
      if (task.CacheStatus is Completed completedCache) {
        HandleStatusUpdate(canVerify, task, completedCache);
      }

      return;
    }

    var incrementedJobs = Interlocked.Increment(ref runningVerificationJobs);
    logger.LogDebug(
      $"Incremented jobs for task, remaining jobs {incrementedJobs}, {Input.Uri} version {Input.Version}");

    statusUpdates.Subscribe(
      update => {
        try {
          HandleStatusUpdate(canVerify, task, update);
        } catch (Exception e) {
          logger.LogError(e, "Caught exception in statusUpdates OnNext.");
        }
      },
      e => {
        updates.OnNext(new BoogieException(canVerify, task, e));
        if (e is not OperationCanceledException) {
          logger.LogError(e, $"Caught error in statusUpdates observable.");
        }
      }
    );
  }

  public async Task Cancel(FilePosition filePosition) {
    var resolution = await Resolution;
    var canVerify = resolution.ResolvedProgram.FindNode<ICanVerify>(filePosition.Uri, filePosition.Position.ToDafnyPosition());
    if (canVerify != null) {
      var implementations = tasksPerVerifiable.TryGetValue(canVerify, out var implementationsPerName)
        ? implementationsPerName! : Enumerable.Empty<IVerificationTask>();
      foreach (var view in implementations) {
        view.Cancel();
      }
      verifyingOrVerifiedSymbols.TryRemove(canVerify, out _);
    }
  }

  private void HandleStatusUpdate(ICanVerify canVerify, IVerificationTask verificationTask, IVerificationStatus boogieStatus) {
    var tokenString = BoogieGenerator.ToDafnyToken(true, verificationTask.Split.Token).TokenToString(Options);
    logger.LogDebug($"Received Boogie status {boogieStatus} for {tokenString}, version {Input.Version}");

    updates.OnNext(new BoogieUpdate(transformedProgram!.ProofDependencyManager, canVerify,
      verificationTask,
      boogieStatus));
  }

  public void CancelPendingUpdates() {
    cancellationSource.Cancel();
  }

  public async Task<TextEditContainer?> GetTextEditToFormatCode(Uri uri) {
    // TODO https://github.com/dafny-lang/dafny/issues/3416
    var program = await ParsedProgram;

    if (program.HasParseErrors) {
      return null;
    }

    var firstToken = program.GetFirstTokenForUri(uri);
    if (firstToken == null) {
      return null;
    }

    // Make sure that we capture the legacy include tokens
    while (firstToken.Prev is { line: >= 1, Filepath: var filePath } && filePath == firstToken.Filepath) {
      firstToken = firstToken.Prev;
    }
    var result = Formatting.__default.ReindentProgramFromFirstToken(firstToken,
      IndentationFormatter.ForProgram(program, firstToken.Uri));

    var lastToken = firstToken;
    while (lastToken.Next != null) {
      lastToken = lastToken.Next;
    }
    // TODO: end position doesn't take into account trailing trivia: https://github.com/dafny-lang/dafny/issues/3415
    return new TextEditContainer(new TextEdit[] {
      new() {NewText = result, Range = new Range(new Position(0,0), lastToken.GetLspPosition())}
    });

  }

  public void Dispose() {
    if (disposed) {
      return;
    }

    disposed = true;
    CancelPendingUpdates();
  }

  public static List<DafnyDiagnostic> GetDiagnosticsFromResult(DafnyOptions options, Uri uri, IVerificationTask task, VerificationRunResult result) {
    var errorReporter = new ObservableErrorReporter(options, uri);
    List<DafnyDiagnostic> diagnostics = new();
    errorReporter.Updates.Subscribe(d => diagnostics.Add(d.Diagnostic));

    ReportDiagnosticsInResult(options, task, result, errorReporter);

    return diagnostics.OrderBy(d => d.Token.GetLspPosition()).ToList();
  }

  public static void ReportDiagnosticsInResult(DafnyOptions options, IVerificationTask task, VerificationRunResult result,
    ErrorReporter errorReporter) {
    var outcome = GetOutcome(result.Outcome);
    result.CounterExamples.Sort(new CounterexampleComparer());
    foreach (var counterExample in result.CounterExamples) //.OrderBy(d => d.GetLocation()))
    {
      errorReporter.ReportBoogieError(counterExample.CreateErrorInformation(outcome, options.ForceBplErrors));
    }

    // This reports problems that are not captured by counter-examples, like a time-out
    // The Boogie API forces us to create a temporary engine here to report the outcome, even though it only uses the options.
    var boogieEngine = new ExecutionEngine(options, new VerificationResultCache(),
      CustomStackSizePoolTaskScheduler.Create(0, 0));
    var implementation = task.Split.Implementation;
    boogieEngine.ReportOutcome(null, outcome, outcomeError => errorReporter.ReportBoogieError(outcomeError, false),
      implementation.VerboseName, implementation.tok, null, TextWriter.Null,
      implementation.GetTimeLimit(options), result.CounterExamples);
  }

  public static VcOutcome GetOutcome(SolverOutcome outcome) {
    switch (outcome) {
      case SolverOutcome.Valid:
        return VcOutcome.Correct;
      case SolverOutcome.Invalid:
        return VcOutcome.Errors;
      case SolverOutcome.TimeOut:
        return VcOutcome.TimedOut;
      case SolverOutcome.OutOfMemory:
        return VcOutcome.OutOfMemory;
      case SolverOutcome.OutOfResource:
        return VcOutcome.OutOfResource;
      case SolverOutcome.Undetermined:
        return VcOutcome.Inconclusive;
      case SolverOutcome.Bounded:
        return VcOutcome.ReachedBound;
      default:
        throw new ArgumentOutOfRangeException(nameof(outcome), outcome, null);
    }
  }
}