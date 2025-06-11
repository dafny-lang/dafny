#nullable enable

using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Help;
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

  /// <summary>
  /// FilePosition is required because the default module lives in multiple files
  /// </summary>
  private readonly LazyConcurrentDictionary<ModuleDefinition,
    Task<IReadOnlyDictionary<ICanVerify, IReadOnlyList<IVerificationTask>>>> translatedModules = new();

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
  public bool ShouldProcessSolverOptions { get; set; } = true;

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
    });

    cancellationSource = new();
    cancellationSource.Token.Register(() => started.TrySetCanceled(cancellationSource.Token));

    verificationTickets.Enqueue(Unit.Default);

    RootFiles = DetermineRootFiles();
    ParsedProgram = ParseAsync();
    Resolution = ResolveAsync();

    _ = LogExceptions();
  }

  private async Task LogExceptions() {
    try {
      await RootFiles;
      await ParsedProgram;
      await Resolution;
    } catch (OperationCanceledException) {
    } catch (Exception e) {
      HandleException(e);
    }
  }

  private void HandleException(Exception e) {
    logger.LogCritical(e, "internal exception");
    updates.OnNext(new InternalCompilationException(MessageSource.Project, e));
  }

  public void Start() {
    if (Started) {
      throw new InvalidOperationException("Compilation was already started");
    }

    Project.Errors.CopyDiagnostics(errorReporter);

    started.TrySetResult();
  }

  private async Task<IReadOnlyList<DafnyFile>> DetermineRootFiles() {
    await started.Task;

    var result = new List<DafnyFile>();

    var handledInput = new HashSet<Uri>();
    foreach (var uri in Options.CliRootSourceUris) {
      if (!handledInput.Add(uri)) {
        continue;
      }
      var shortPath = Path.GetRelativePath(Directory.GetCurrentDirectory(), uri.LocalPath);
      await foreach (var file in DafnyFile.CreateAndValidate(fileSystem, errorReporter, Options, uri, Token.Cli,
                       false,
                       $"command-line argument '{shortPath}' is neither a recognized option nor a Dafny input file (.dfy, .doo, or .toml).")) {
        result.Add(file);
      }
    }

    var includedFiles = new List<DafnyFile>();
    foreach (var uri in Input.Project.GetRootSourceUris(fileSystem)) {
      if (!handledInput.Add(uri)) {
        continue;
      }
      await foreach (var file in DafnyFile.CreateAndValidate(fileSystem, errorReporter, Options, uri,
                       Project.StartingToken)) {
        result.Add(file);
        includedFiles.Add(file);
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
      if (Options.Backend is LibraryBackend) {
        Options.Set(CommonOptionBag.TranslateStandardLibrary, false);
      }

      // For now the standard libraries are still translated from scratch.
      // This creates issues with separate compilation and will be addressed in https://github.com/dafny-lang/dafny/pull/4877
      var asLibrary = !Options.Get(CommonOptionBag.TranslateStandardLibrary);

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

    var libraryPaths = CommonOptionBag.SplitOptionValueIntoFiles(Options.GetOrOptionDefault(CommonOptionBag.Libraries).Select(f => f.FullName));
    foreach (var library in libraryPaths) {
      await foreach (var file in DafnyFile.CreateAndValidate(fileSystem, errorReporter, Options, new Uri(library), Project.StartingToken, true)) {
        result.Add(file);
      }
    }

    if (Project.UsesProjectFile) {
      var projectDirectory = Path.GetDirectoryName(Project.Uri.LocalPath)!;
      var includedRootsMessage = string.Join("\n", includedFiles.Select(dafnyFile => Path.GetRelativePath(projectDirectory, dafnyFile.Uri.LocalPath)));
      if (includedRootsMessage == "") {
        includedRootsMessage = "none";
      }
      errorReporter.Info(MessageSource.Project, Project.StartingToken, "Files included by project are:" + Environment.NewLine + includedRootsMessage);
    }

    // Allow specifying the same file twice on the CLI
    var distinctResults = result.DistinctBy(d => d.Uri).ToList();

    updates.OnNext(new DeterminedRootFiles(Project, distinctResults));
    return distinctResults;
  }

  private async Task<Program?> ParseAsync() {
    await RootFiles;
    if (HasErrors) {
      return null;
    }

    var parseResult = await documentLoader.ParseAsync(this, cancellationSource.Token);
    if (Options.Get(CommonOptionBag.CheckSourceLocationConsistency)) {
      CheckSourceLocationConsistency(null, parseResult.Program);
    }

    transformedProgram = parseResult.Program;
    transformedProgram.HasParseErrors = HasErrors;

    var cloner = new Cloner(true);
    programAfterParsing = new Program(cloner, transformedProgram);

    updates.OnNext(new FinishedParsing(parseResult with { Program = programAfterParsing }));
    logger.LogDebug(
      $"Passed parsedCompilation to documentUpdates.OnNext, resolving ParsedCompilation task for version {Input.Version}.");
    return programAfterParsing;
  }

  private void CheckSourceLocationConsistency(INode? container, INode node) {
    var nodeRange = node.EntireRange;
    if (container != null) {
      var containerRange = container.EntireRange;
      if (nodeRange.Uri != null) {
        var contained = containerRange.StartToken.LessThanOrEquals(nodeRange.StartToken) &&
                        nodeRange.EndToken.LessThanOrEquals(containerRange.EndToken);
        if (!contained) {
          throw new Exception(
            $"Range of parent node ({container}) did not contain range of child node ({node}):\n" +
            $"    {containerRange} does not contain {nodeRange}");
        }
      }
    }

    foreach (var child in node.PreResolveChildren) {
      CheckSourceLocationConsistency(node.Origin.Uri == null ? container : node, child);
    }
  }

  private async Task<ResolutionResult?> ResolveAsync() {
    await ParsedProgram;
    if (transformedProgram == null) {
      return null;
    }
    var resolution = await documentLoader.ResolveAsync(this, transformedProgram!, cancellationSource.Token);
    if (resolution == null) {
      return null;
    }

    updates.OnNext(new FinishedResolution(resolution));
    staticDiagnosticsSubscription.Dispose();
    logger.LogDebug($"Passed resolvedCompilation to documentUpdates.OnNext, resolving ResolvedCompilation task for version {Input.Version}.");
    return resolution;
  }

  public static string GetTaskName(IVerificationTask task) {
    var prefix = task.ScopeId + task.Split.SplitIndex;

    // Refining declarations get the token of what they're refining, so to distinguish them we need to
    // add the refining module name to the prefix.
    if (task.ScopeToken is RefinementOrigin refinementToken) {
      prefix += "." + refinementToken.InheritingModule.Name;
    }

    return prefix;
  }

  // When verifying a symbol, a ticket must be acquired before the SMT part of verification may start.
  private readonly AsyncQueue<Unit> verificationTickets = new();
  public async Task<bool> VerifyLocation(FilePosition verifiableLocation, Func<IVerificationTask, bool>? taskFilter = null,
    int? randomSeed = null,
    bool onlyPrepareVerificationForGutterTests = false) {
    cancellationSource.Token.ThrowIfCancellationRequested();

    var resolution = await Resolution;
    if (resolution == null || resolution.HasErrors) {
      return false;
    }

    var canVerifies = GetCanVerify(verifiableLocation, resolution);

    var result = false;
    foreach (var canVerify in canVerifies) {
      result |= await VerifyCanVerify(canVerify, taskFilter ?? (_ => true), randomSeed, onlyPrepareVerificationForGutterTests);
    }

    return result;
  }

  private static IEnumerable<ICanVerify> GetCanVerify(
    FilePosition verifiableLocation,
    ResolutionResult resolution) {
    if (resolution.CanVerifies?.TryGetValue(verifiableLocation.Uri, out var canVerifyForUri) == true) {
      var canVerifies = canVerifyForUri.Query(verifiableLocation.Position.ToDafnyPosition());
      return canVerifies;
    }

    return [];
  }

  public async Task<bool> VerifyCanVerify(ICanVerify canVerify, Func<IVerificationTask, bool> taskFilter,
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

    if (!onlyPrepareVerificationForGutterTests && (randomSeed == null && !verifyingOrVerifiedSymbols.TryAdd(canVerify, Unit.Default))) {
      return false;
    }

    updates.OnNext(new ScheduledVerification(canVerify));

    if (onlyPrepareVerificationForGutterTests) {
      await VerifyUnverifiedSymbol(onlyPrepareVerificationForGutterTests, canVerify, resolution, taskFilter, randomSeed);
      return true;
    }

    _ = VerifyUnverifiedSymbol(onlyPrepareVerificationForGutterTests, canVerify, resolution, taskFilter, randomSeed);
    return true;
  }

  private async Task VerifyUnverifiedSymbol(bool onlyPrepareVerificationForGutterTests, ICanVerify canVerify,
    ResolutionResult resolution, Func<IVerificationTask, bool> taskFilter, int? randomSeed) {
    try {

      var ticket = verificationTickets.Dequeue();
      var containingModule = canVerify.ContainingModule;

      IReadOnlyDictionary<ICanVerify, IReadOnlyList<IVerificationTask>> tasksForModule;
      try {
        tasksForModule = await translatedModules.GetOrAdd(containingModule, async () => {
          var result = await verifier.GetVerificationTasksAsync(boogieEngine, resolution, containingModule,
            cancellationSource.Token);

          return result.GroupBy(t => {
            var dafnyToken = (CanVerifyOrigin)t.ScopeToken;
            return dafnyToken.CanVerify;
          }).ToDictionary(
            g => g.Key,
            g => (IReadOnlyList<IVerificationTask>)g.ToList());
        });
      } catch (OperationCanceledException) {
        throw;
      } catch (Exception e) {
        HandleException(e);
        throw;
      }

      // For updated to be reliable, tasksPerVerifiable must be Lazy
      var updated = false;
      var tasks = tasksPerVerifiable.GetOrAdd(canVerify, () => {
        var result =
          tasksForModule.GetValueOrDefault(canVerify) ??
          new List<IVerificationTask>(0);

        updated = true;
        return result;
      });
      if (updated || randomSeed != null) {
        updates.OnNext(new CanVerifyPartsIdentified(canVerify, tasks));
      }

      // When multiple calls to VerifyUnverifiedSymbol are made, the order in which they pass this await matches the call order.
      await ticket;

      if (!onlyPrepareVerificationForGutterTests) {
        var groups = GroupOverlappingRanges(tasks).
          OrderBy(g => g.Group.StartToken);
        foreach (var tokenTasks in groups) {
          var functions = tokenTasks.Tasks.SelectMany(t => t.Split.HiddenFunctions.Select(f => f.tok).
            OfType<FromDafnyNode>().Select(n => n.Node).
            OfType<Function>()).Distinct().OrderBy(f => f.Origin.Center);
          var hiddenFunctions = string.Join(", ", functions.Select(f => f.FullDafnyName));
          if (!string.IsNullOrEmpty(hiddenFunctions)) {
            Reporter.Info(MessageSource.Verifier,
              new SourceOrigin(tokenTasks.Group.StartToken, tokenTasks.Group.EndToken),
              $"hidden functions: {hiddenFunctions}");
          }
        }

        foreach (var task in tasks.Where(taskFilter)) {

          var seededTask = randomSeed == null ? task : task.FromSeed(randomSeed.Value);
          VerifyTask(canVerify, seededTask);
        }
      }

    }
    finally {
      verificationTickets.Enqueue(Unit.Default);
    }
  }


  public static IEnumerable<(TokenRange Group, List<IVerificationTask> Tasks)> GroupOverlappingRanges(IReadOnlyList<IVerificationTask> ranges) {
    if (!ranges.Any()) {
      return [];
    }
    var sortedTasks = ranges.OrderBy(r =>
      BoogieGenerator.ToDafnyToken(r.Token).ReportingRange.StartToken).ToList();
    var groups = new List<(TokenRange Group, List<IVerificationTask> Tasks)>();
    var currentGroup = new List<IVerificationTask> { sortedTasks[0] };
    var currentGroupRange = BoogieGenerator.ToDafnyToken(currentGroup[0].Token).ReportingRange;

    for (int i = 1; i < sortedTasks.Count; i++) {
      var currentTask = sortedTasks[i];
      var currentTaskRange = BoogieGenerator.ToDafnyToken(currentTask.Token).ReportingRange;
      bool overlapsWithGroup = currentGroupRange.Intersects(currentTaskRange);

      if (overlapsWithGroup) {
        if (currentTaskRange.EndToken!.pos > currentGroupRange.EndToken!.pos) {
          currentGroupRange = new TokenRange(currentGroupRange.StartToken!, currentTaskRange.EndToken);
        }
        currentGroup.Add(currentTask);
      } else {
        groups.Add((currentGroupRange, currentGroup));
        currentGroup = [currentTask];
        currentGroupRange = currentTaskRange;
      }
    }

    groups.Add((currentGroupRange, currentGroup)); // Add the last group
    return groups;
  }

  private void VerifyTask(ICanVerify canVerify, IVerificationTask task) {
    var statusUpdates = task.TryRun();
    if (statusUpdates == null) {
      if (task.CacheStatus is Completed completedCache) {
        HandleStatusUpdate(canVerify, task, completedCache);
      }

      return;
    }

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
    if (resolution == null) {
      return;
    }

    var canVerifies = GetCanVerify(filePosition, resolution);
    foreach (var canVerify in canVerifies) {
      var implementations = tasksPerVerifiable.TryGetValue(canVerify, out var implementationsPerName)
        ? implementationsPerName! : Enumerable.Empty<IVerificationTask>();
      foreach (var view in implementations) {
        view.Cancel();
      }
      verifyingOrVerifiedSymbols.TryRemove(canVerify, out _);
    }
  }

  private void HandleStatusUpdate(ICanVerify canVerify, IVerificationTask verificationTask, IVerificationStatus boogieStatus) {
    var tokenString = BoogieGenerator.ToDafnyToken(verificationTask.Split.Token).OriginToString(Options);
    logger.LogDebug($"Received Boogie status {boogieStatus} for {tokenString}, version {Input.Version}");

    updates.OnNext(new BoogieUpdate(transformedProgram!.ProofDependencyManager, canVerify,
      verificationTask,
      boogieStatus));
  }

  public void CancelPendingUpdates() {
    cancellationSource.Cancel();
    foreach (var (_, tasks) in tasksPerVerifiable) {
      foreach (var task in tasks) {
        task.Cancel();
      }
    }
  }

  public async Task<TextEditContainer?> GetTextEditToFormatCode(Uri uri) {
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
    return new TextEditContainer([
      new() { NewText = result, Range = new Range(new Position(0, 0), lastToken.GetLspPosition()) }
    ]);

  }

  public void Dispose() {
    if (disposed) {
      return;
    }

    disposed = true;
    CancelPendingUpdates();
  }

  public static List<DafnyDiagnostic> GetDiagnosticsFromResult(DafnyOptions options, Uri uri, ICanVerify canVerify,
    IVerificationTask task, VerificationRunResult result) {
    var errorReporter = new ObservableErrorReporter(options, uri);
    List<DafnyDiagnostic> diagnostics = [];
    errorReporter.Updates.Subscribe(d => diagnostics.Add(d.Diagnostic));

    ReportDiagnosticsInResult(options, canVerify.NavigationRange.StartToken.val, BoogieGenerator.ToDafnyToken(task.Token),
      task.Split.Implementation.GetTimeLimit(options), result, errorReporter);

    return diagnostics.OrderBy(d => d.Range.StartToken.GetLspPosition()).ToList();
  }

  public static void ReportDiagnosticsInResult(DafnyOptions options, string name, IOrigin token,
    uint timeLimit,
    VerificationRunResult result,
    ErrorReporter errorReporter) {
    var outcome = GetOutcome(result.Outcome);
    result.CounterExamples.Sort(new CounterexampleComparer());
    foreach (var counterExample in result.CounterExamples) {
      var description = counterExample.FailingAssert.Description as ProofObligationDescription;
      var dafnyDiagnostic = description?.GetDiagnostic(
        BoogieGenerator.ToDafnyToken(counterExample.FailingAssert.tok).ReportingRange);
      if (options.Get(CommonOptionBag.JsonOutput) && dafnyDiagnostic != null) {
        errorReporter.MessageCore(dafnyDiagnostic);
      } else {
        var errorInformation = counterExample.CreateErrorInformation(outcome, options.ForceBplErrors);
        if (options.ShowProofObligationExpressions) {
          AddAssertedExprToCounterExampleErrorInfo(options, counterExample, errorInformation);
        }
        var dafnyCounterExampleModel = options.ExtractCounterexample ? new DafnyModel(counterExample.Model, options) : null;
        errorReporter.ReportBoogieError(errorInformation, dafnyCounterExampleModel);
      }
    }

    var outcomeError = ReportOutcome(options, outcome, name, token, timeLimit, result.CounterExamples);
    if (outcomeError != null) {
      errorReporter.ReportBoogieError(outcomeError, null, false);
    }
  }

  private static ErrorInformation? ReportOutcome(DafnyOptions options,
      VcOutcome vcOutcome, string name,
      IToken token, uint timeLimit, List<Counterexample> errors) {
    ErrorInformation? errorInfo = null;

    switch (vcOutcome) {
      case VcOutcome.Correct:
        break;
      case VcOutcome.Errors:
      case VcOutcome.TimedOut: {
          if (vcOutcome != VcOutcome.TimedOut &&
              (!errors.Any(e => e.IsAuxiliaryCexForDiagnosingTimeouts))) {
            break;
          }

          string msg = string.Format("Verification of '{1}' timed out after {0} seconds. (the limit can be increased using --verification-time-limit)", timeLimit, name);
          errorInfo = ErrorInformation.Create(new SourceOrigin(BoogieGenerator.ToDafnyToken(token).ReportingRange), msg);

          //  Report timed out assertions as auxiliary info.
          var comparer = new CounterexampleComparer();
          var timedOutAssertions = errors.Where(e => e.IsAuxiliaryCexForDiagnosingTimeouts).Distinct(comparer)
            .OrderBy(x => x, comparer).ToList();
          if (0 < timedOutAssertions.Count) {
            errorInfo!.Msg += $" with {timedOutAssertions.Count} check(s) that timed out individually";
          }

          foreach (Counterexample error in timedOutAssertions) {
            IToken tok;
            string auxMsg = null!;
            switch (error) {
              case CallCounterexample callCounterexample:
                tok = callCounterexample.FailingCall.tok;
                auxMsg = callCounterexample.FailingCall.Description.FailureDescription;
                break;
              case ReturnCounterexample returnCounterexample:
                tok = returnCounterexample.FailingReturn.tok;
                auxMsg = returnCounterexample.FailingReturn.Description.FailureDescription;
                break;
              case AssertCounterexample assertError: {
                  tok = assertError.FailingAssert.tok;
                  if (!(assertError.FailingAssert.ErrorMessage == null ||
                        ((ExecutionEngineOptions)options).ForceBplErrors)) {
                    auxMsg = assertError.FailingAssert.ErrorMessage;
                  }

                  auxMsg ??= assertError.FailingAssert.Description.FailureDescription;
                  break;
                }
              default: throw new Exception();
            }

            errorInfo.AddAuxInfo(tok, auxMsg, "Unverified check due to timeout");
          }

          break;
        }
      case VcOutcome.OutOfResource: {
          var dafnyToken = BoogieGenerator.ToDafnyToken(token);
          string msg = "Verification out of resource (" + name + ")";
          errorInfo = ErrorInformation.Create(dafnyToken.ReportingRange.StartToken, msg);
        }
        break;
      case VcOutcome.OutOfMemory: {
          string msg = "Verification out of memory (" + name + ")";
          errorInfo = ErrorInformation.Create(token, msg);
        }
        break;
      case VcOutcome.SolverException: {
          string msg = "Verification encountered solver exception (" + name + ")";
          errorInfo = ErrorInformation.Create(token, msg);
        }
        break;

      case VcOutcome.Inconclusive: {
          string msg = "Verification inconclusive (" + name + ")";
          errorInfo = ErrorInformation.Create(token, msg);
        }
        break;
    }

    return errorInfo;
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

    if (boogieProofObligationDesc is ProofObligationDescription dafnyProofObligationDesc) {
      var expr = dafnyProofObligationDesc.GetAssertedExpr(options);
      string? msg = null;
      if (expr != null) {
        msg = expr.ToString();
      }

      var extra = dafnyProofObligationDesc.GetExtraExplanation();
      if (extra != null) {
        msg = (msg ?? "") + extra;
      }

      if (msg != null) {
        errorInformation.AddAuxInfo(errorInformation.Tok, msg,
          ErrorReporterExtensions.AssertedExprCategory);
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
        return VcOutcome.Correct;
      default:
        throw new ArgumentOutOfRangeException(nameof(outcome), outcome, null);
    }
  }

  public void ClearModuleCache(ModuleDefinition moduleDefinition) {
    translatedModules.Remove(moduleDefinition);
  }

  public void ClearCanVerifyCache(ICanVerify canVerify) {
    tasksPerVerifiable.Remove(canVerify);
  }
}