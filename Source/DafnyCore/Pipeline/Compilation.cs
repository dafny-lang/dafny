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
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using VC;
using VCGeneration;
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

  /// <summary>
  /// FilePosition is required because the default module lives in multiple files
  /// </summary>
  private readonly LazyConcurrentDictionary<ModuleDefinition,
    Task<IReadOnlyDictionary<FilePosition, IReadOnlyList<IVerificationTask>>>> translatedModules = new();

  private readonly ConcurrentDictionary<ICanVerify, Unit> verifyingOrVerifiedSymbols = new();
  private readonly LazyConcurrentDictionary<ICanVerify, IReadOnlyList<IVerificationTask>> tasksPerVerifiable = new();

  public DafnyOptions Options => Input.Options;
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

  public Task<Program?> ParsedProgram { get; }
  public Task<ResolutionResult?> Resolution { get; }

  public ErrorReporter Reporter => errorReporter;

  public Task<IReadOnlyList<DafnyFile>> RootFiles { get; set; }
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

    RootFiles = DetermineRootFiles();
    ParsedProgram = ParseAsync();
    Resolution = ResolveAsync();
  }

  public void Start() {
    if (Started) {
      throw new InvalidOperationException("Compilation was already started");
    }

    Project.Errors.CopyDiagnostics(errorReporter);

    // updates.OnNext(new PhaseDiscovered(RootPhase.Instance,
    //   Enum.GetValues<MessageSource>().Select(s => (IPhase)new MessageSourceBasedPhase(s)).ToHashSet()));

    started.TrySetResult();
  }

  private ImmutableList<FileDiagnostic> GetDiagnosticsCopyAndClear() {
    var result = staticDiagnostics.SelectMany(k =>
      k.Value.Select(v => new FileDiagnostic(k.Key, v.ToLspDiagnostic()))).ToImmutableList();
    staticDiagnostics.Clear();
    return result;
  }



  private async Task<IReadOnlyList<DafnyFile>> DetermineRootFiles() {
    await started.Task;

    var result = new List<DafnyFile>();

    foreach (var uri in Input.Project.GetRootSourceUris(fileSystem)) {
      await foreach (var file in DafnyFile.CreateAndValidate(fileSystem, errorReporter, Options, uri,
                       Project.StartingToken)) {
        result.Add(file);
      }
    }

    foreach (var uri in Options.CliRootSourceUris) {
      var shortPath = Path.GetRelativePath(Directory.GetCurrentDirectory(), uri.LocalPath);
      await foreach (var file in DafnyFile.CreateAndValidate(fileSystem, errorReporter, Options, uri, Token.Cli,
                       false,
                       $"command-line argument '{shortPath}' is neither a recognized option nor a Dafny input file (.dfy, .doo, or .toml).")) {
        result.Add(file);
      }
    }
    if (Options.UseStdin) {
      result.Add(DafnyFile.HandleStandardInput(Options, Token.Cli));
    }

    if (!HasErrors && !result.Any()) {
      errorReporter.Error(MessageSource.Project, GeneratorErrors.ErrorId.None, Project.StartingToken,
        "no Dafny source files were specified as input");
    }

    if (Options.Get(CommonOptionBag.UseStandardLibraries)) {
      // For now the standard libraries are still translated from scratch.
      // This breaks separate compilation and will be addressed in https://github.com/dafny-lang/dafny/pull/4877
      var asLibrary = false;

      if (Options.CompilerName is null or "cs" or "java" or "go" or "py" or "js") {
        var targetName = Options.CompilerName ?? "notarget";
        var stdlibDooUri = DafnyMain.StandardLibrariesDooUriTarget[targetName];
        await foreach (var targetSpecificFile in DafnyFile.CreateAndValidate(OnDiskFileSystem.Instance, errorReporter,
                         Options, stdlibDooUri, Project.StartingToken, asLibrary)) {
          result.Add(targetSpecificFile);
        }
      }

      await foreach (var file in DafnyFile.CreateAndValidate(fileSystem, errorReporter, Options,
                       DafnyMain.StandardLibrariesDooUri, Project.StartingToken, asLibrary)) {
        result.Add(file);
      }
    }

    var libraryFiles = CommonOptionBag.SplitOptionValueIntoFiles(Options.Get(CommonOptionBag.Libraries).Select(f => f.FullName));
    foreach (var library in libraryFiles) {
      await foreach (var file in DafnyFile.CreateAndValidate(fileSystem, errorReporter, Options, new Uri(library), Project.StartingToken, true)) {
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

    // Allow specifying the same file twice on the CLI
    var distinctResults = result.DistinctBy(d => d.Uri).ToList();

    updates.OnNext(new DeterminedRootFiles(Project, distinctResults, GetDiagnosticsCopyAndClear()));

    updates.OnNext(new PhaseFinished(new MessageSourceBasedPhase(MessageSource.Project)));
    return distinctResults;
  }

  private async Task<Program?> ParseAsync() {
    try {
      await RootFiles;
      if (HasErrors) {
        return null;
      }

      transformedProgram = await documentLoader.ParseAsync(this, cancellationSource.Token);
      transformedProgram.HasParseErrors = HasErrors;

      var cloner = new Cloner(true);
      programAfterParsing = new Program(cloner, transformedProgram);

      updates.OnNext(new FinishedParsing(programAfterParsing, GetDiagnosticsCopyAndClear()));
      logger.LogDebug(
        $"Passed parsedCompilation to documentUpdates.OnNext, resolving ParsedCompilation task for version {Input.Version}.");
      updates.OnNext(new PhaseFinished(new MessageSourceBasedPhase(MessageSource.Parser)));
      return programAfterParsing;

    } catch (OperationCanceledException) {
      throw;
    } catch (Exception e) {
      updates.OnNext(new InternalCompilationException(new MessageSourceBasedPhase(MessageSource.Parser), e));
      throw;
    }
  }

  private async Task<ResolutionResult?> ResolveAsync() {
    try {
      await ParsedProgram;
      if (transformedProgram == null) {
        return null;
      }
      var resolution = await documentLoader.ResolveAsync(this, transformedProgram!, cancellationSource.Token);
      if (resolution == null) {
        return null;
      }

      updates.OnNext(new FinishedResolution(
        resolution,
        GetDiagnosticsCopyAndClear()));
      var canVerifies = resolution.CanVerifies ?? Array.Empty<ICanVerify>();
      updates.OnNext(new PhaseDiscovered(new MessageSourceBasedPhase(MessageSource.Verifier),
        canVerifies.Select(c => (IPhase)new VerificationOfSymbol(c)).ToHashSet()));

      staticDiagnosticsSubscription.Dispose();
      updates.OnNext(new PhaseFinished(new MessageSourceBasedPhase(MessageSource.Cloner)));
      updates.OnNext(new PhaseFinished(new MessageSourceBasedPhase(MessageSource.RefinementTransformer)));
      updates.OnNext(new PhaseFinished(new MessageSourceBasedPhase(MessageSource.Rewriter)));
      updates.OnNext(new PhaseFinished(new MessageSourceBasedPhase(MessageSource.Resolver)));

      updates.OnNext(new PhaseFinished(new MessageSourceBasedPhase(MessageSource.Translator)));
      //Project, Parser, Cloner, RefinementTransformer, Rewriter, Resolver, Translator, Verifier, Compiler, Documentation, TestGeneration, Unknown
      logger.LogDebug($"Passed resolvedCompilation to documentUpdates.OnNext, resolving ResolvedCompilation task for version {Input.Version}.");
      return resolution;

    } catch (OperationCanceledException) {
      throw;
    } catch (Exception e) {
      updates.OnNext(new InternalCompilationException(new MessageSourceBasedPhase(MessageSource.Resolver), e));
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

  // When verifying a symbol, a ticket must be acquired before the SMT part of verification may start.
  private readonly AsyncQueue<Unit> verificationTickets = new();
  public async Task<bool> VerifyLocation(FilePosition verifiableLocation,
    bool onlyPrepareVerificationForGutterTests = false) {
    cancellationSource.Token.ThrowIfCancellationRequested();

    var resolution = await Resolution;
    if (resolution == null || resolution.HasErrors) {
      return false;
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

    return await VerifyCanVerify(canVerify, null, null, onlyPrepareVerificationForGutterTests);
  }

  public async Task<bool> VerifyCanVerify(ICanVerify canVerify, Func<IVerificationTask, bool>? taskFilter,
    int? randomSeed = 0,
    bool onlyPrepareVerificationForGutterTests = false) {

    var resolution = await Resolution;
    if (resolution == null) {
      return false;
    }

    var containingModule = canVerify.ContainingModule;
    if (!containingModule.ShouldVerify(resolution.ResolvedProgram.Compilation)) {
      return false;
    }

    if (onlyPrepareVerificationForGutterTests) {
      await VerifyUnverifiedSymbol(canVerify, resolution, _ => false, randomSeed);
      return true;
    }

    if ((randomSeed == null && !verifyingOrVerifiedSymbols.TryAdd(canVerify, Unit.Default))) {
      return false;
    }

    updates.OnNext(new ScheduledVerification(canVerify));

    _ = VerifyUnverifiedSymbol(canVerify, resolution, taskFilter, randomSeed);
    return true;
  }

  private async Task VerifyUnverifiedSymbol(ICanVerify canVerify,
    ResolutionResult resolution, Func<IVerificationTask, bool>? taskFilter, int? randomSeed) {

    var verificationOfSymbol = new VerificationOfSymbol(canVerify);
    if (taskFilter == null) {
      updates.OnNext(new PhaseStarted(verificationOfSymbol));
    }
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
        updates.OnNext(new InternalCompilationException(new MessageSourceBasedPhase(MessageSource.Verifier), e));
        throw;
      }

      // For updated to be reliable, tasksPerVerifiable must be Lazy
      var updated = false;
      IReadOnlyList<IVerificationTask> verificationTasks = tasksPerVerifiable.GetOrAdd(canVerify, () => {
        var result =
          tasksForModule.GetValueOrDefault(canVerify.NameToken.GetFilePosition()) ??
          new List<IVerificationTask>(0);

        updated = true;
        return result;
      });
      if (updated || randomSeed != null) {
        updates.OnNext(new CanVerifyPartsIdentified(canVerify,
          tasksPerVerifiable[canVerify].ToList()));
      }

      // When multiple calls to VerifyUnverifiedSymbol are made, the order in which they pass this await matches the call order.
      await ticket;

      var filteredVerificationTasks = taskFilter == null ? verificationTasks : verificationTasks.Where(taskFilter);
      var verificationTaskPerScope = filteredVerificationTasks.GroupBy(t => t.ScopeId).ToList();

      updates.OnNext(new PhaseDiscovered(verificationOfSymbol,
        verificationTaskPerScope.Select(s =>
          (IPhase)new VerificationOfScope(verificationOfSymbol, s.Key)).ToHashSet()));
      var tasksForSymbol = new List<Task<IVerificationStatus>>();

      foreach (var scope in verificationTaskPerScope) {

        var scopePhase = new VerificationOfScope(verificationOfSymbol, scope.Key);

        var scopeVerificationTasks = scope.ToList();
        updates.OnNext(new PhaseDiscovered(scopePhase,
          scopeVerificationTasks.Select(t => (IPhase)new VerificationOfTask(scopePhase)).ToHashSet()));

        var tasksForScope = new List<Task<IVerificationStatus>>();
        foreach (var verificationTask in scopeVerificationTasks) {
          var seededTask = randomSeed == null ? verificationTask : verificationTask.FromSeed(randomSeed.Value);
          var task = VerifyTask(canVerify, seededTask);
          tasksForScope.Add(task);
          tasksForSymbol.Add(task);

          // In master, the verification diagnostics get cleared when the thing starts running.
          // We don't have a good key for a task.
          _ = HandleTaskFinished();
          async Task HandleTaskFinished() {
            var status = await task;
            var phase = new VerificationOfTask(scopePhase);
            if (status is Completed completed) {
              ReportDiagnosticsInResult(Options, phase, canVerify.FullDafnyName, verificationTask.Token,
                (uint)completed.Result.RunTime.Seconds,
                completed.Result, errorReporter);
            }
            updates.OnNext(new PhaseFinished(phase));
          }
        }

        _ = HandleScopeFinishedVerification();
        async Task HandleScopeFinishedVerification() {
          if (taskFilter != null) {
            return;
          }
          var statuses = await Task.WhenAll(tasksForScope);
          if (statuses.Any(s => s is Stale)) {
            return;
          }

          ProofDependencyWarnings.WarnAboutSuspiciousDependenciesForScope(Options, scopePhase,
            errorReporter, transformedProgram!.ProofDependencyManager, scope.Key, statuses.Select(s => ((Completed)s).Result).ToList());

        }
      }

      _ = HandleSymbolFinishedVerification();
      async Task HandleSymbolFinishedVerification() {
        if (taskFilter != null) {
          return;
        }
        var statuses = await Task.WhenAll(tasksForSymbol);
        if (statuses.Any(s => s is Stale)) {
          return;
        }

        updates.OnNext(new PhaseFinished(verificationOfSymbol));
      }
    }
    finally {
      verificationTickets.Enqueue(Unit.Default);
    }
  }

  private Task<IVerificationStatus> VerifyTask(ICanVerify canVerify, IVerificationTask task) {
    var statusUpdates = task.TryRun();
    if (statusUpdates == null) {
      if (task.CacheStatus is Completed completedCache) {
        HandleStatusUpdate(canVerify, task, completedCache);
      }

      return Task.FromResult(task.CacheStatus);
    }

    var completed = new TaskCompletionSource<IVerificationStatus>();
    statusUpdates.Subscribe(
      update => {
        try {
          if (update is Completed or Stale) {
            completed.TrySetResult(update);
          }
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
    return completed.Task;
  }

  public async Task Cancel(FilePosition filePosition) {
    var resolution = await Resolution;
    if (resolution == null) {
      return;
    }

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
    if (program == null) {
      return null;
    }

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

  private static void ReportDiagnosticsInResult(DafnyOptions options, IPhase phase, string name, Boogie.IToken token,
    uint timeLimit,
    VerificationRunResult result,
    ErrorReporter errorReporter) {
    var outcome = GetOutcome(result.Outcome);
    result.CounterExamples.Sort(new CounterexampleComparer());
    foreach (var counterExample in result.CounterExamples) //.OrderBy(d => d.GetLocation()))
    {
      var errorInformation = counterExample.CreateErrorInformation(outcome, options.ForceBplErrors);
      if (options.ShowProofObligationExpressions) {
        AddAssertedExprToCounterExampleErrorInfo(options, counterExample, errorInformation);
      }
      var dafnyCounterExampleModel = options.ExtractCounterexample ? new DafnyModel(counterExample.Model, options) : null;
      errorReporter.ReportBoogieError(phase, errorInformation, dafnyCounterExampleModel);
    }

    // This reports problems that are not captured by counter-examples, like a time-out
    // The Boogie API forces us to create a temporary engine here to report the outcome, even though it only uses the options.
    var boogieEngine = new ExecutionEngine(options, new VerificationResultCache(),
      CustomStackSizePoolTaskScheduler.Create(0, 0));
    boogieEngine.ReportOutcome(null, outcome, outcomeError => errorReporter.ReportBoogieError(phase, outcomeError, null, false),
      name, token, null, TextWriter.Null,
      timeLimit, result.CounterExamples);
  }

  private static void AddAssertedExprToCounterExampleErrorInfo(
      DafnyOptions options, Counterexample counterExample, ErrorInformation errorInformation) {
    Boogie.ProofObligationDescription? boogieProofObligationDesc = null;
    switch (errorInformation.Kind) {
      case ErrorKind.Assertion:
        boogieProofObligationDesc = ((AssertCounterexample)counterExample).FailingAssert.Description;
        break;
      case ErrorKind.Precondition:
        boogieProofObligationDesc = ((CallCounterexample)counterExample).FailingCall.Description;
        break;
      case ErrorKind.Postcondition:
        boogieProofObligationDesc = ((ReturnCounterexample)counterExample).FailingReturn.Description;
        break;
      case ErrorKind.InvariantEntry:
      case ErrorKind.InvariantMaintainance:
        AssertCmd failingAssert = ((AssertCounterexample)counterExample).FailingAssert;
        if (failingAssert is LoopInitAssertCmd loopInitAssertCmd) {
          boogieProofObligationDesc = loopInitAssertCmd.originalAssert.Description;
        } else if (failingAssert is LoopInvMaintainedAssertCmd maintainedAssertCmd) {
          boogieProofObligationDesc = maintainedAssertCmd.originalAssert.Description;
        }
        break;
      default:
        throw new ArgumentOutOfRangeException($"Unexpected ErrorKind: {errorInformation.Kind}");
    }

    if (boogieProofObligationDesc is ProofObligationDescription.ProofObligationDescription dafnyProofObligationDesc) {
      var expr = dafnyProofObligationDesc.GetAssertedExpr(options);
      if (expr != null) {
        errorInformation.AddAuxInfo(errorInformation.Tok, expr.ToString(), ErrorReporterExtensions.AssertedExprCategory);
      }
    }
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