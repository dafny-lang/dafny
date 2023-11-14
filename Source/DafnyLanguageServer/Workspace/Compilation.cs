using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive;
using System.Reactive.Disposables;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public delegate Compilation CreateCompilation(
  DafnyOptions options,
  ExecutionEngine boogieEngine,
  CompilationInput compilation);

/// <summary>
/// The compilation of a single document version.
/// The document will be parsed, resolved, translated to Boogie and verified.
///
/// Compilation may be configured to pause after translation,
/// requiring a call to Compilation.VerifySymbol for the document to be verified.
///
/// Compilation is agnostic to document updates, it does not handle the migration of old document state.
/// </summary>
public class Compilation : IDisposable {

  private readonly ILogger logger;
  private readonly ITextDocumentLoader documentLoader;
  private readonly IProgramVerifier verifier;

  private readonly TaskCompletionSource started = new();
  private readonly CancellationTokenSource cancellationSource;
  private readonly ConcurrentDictionary<Uri, ConcurrentStack<DafnyDiagnostic>> staticDiagnostics = new();
  public DafnyDiagnostic[] GetDiagnosticsForUri(Uri uri) =>
    staticDiagnostics.TryGetValue(uri, out var forUri) ? forUri.ToArray() : Array.Empty<DafnyDiagnostic>();

  /// <summary>
  /// FilePosition is required because the default module lives in multiple files
  /// </summary>
  private readonly LazyConcurrentDictionary<ModuleDefinition,
    Task<IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>>>> translatedModules = new();

  private readonly ConcurrentDictionary<ICanVerify, Unit> verifyingOrVerifiedSymbols = new();
  private readonly LazyConcurrentDictionary<ICanVerify, Dictionary<string, IImplementationTask>> implementationsPerVerifiable = new();

  private TaskCompletionSource verificationCompleted = new();
  private readonly DafnyOptions options;
  public CompilationInput Input { get; }
  private readonly ExecutionEngine boogieEngine;

  private readonly Subject<ICompilationEvent> updates = new();
  public IObservable<ICompilationEvent> Updates => updates;

  private Program? programAfterParsing;
  private Program? transformedProgram;
  private IDisposable staticDiagnosticsSubscription = Disposable.Empty;

  public Task<Program> Program { get; }
  public Task<ResolutionResult> Resolution { get; }

  public Compilation(
    ILogger<Compilation> logger,
    ITextDocumentLoader documentLoader,
    IProgramVerifier verifier,
    DafnyOptions options,
    ExecutionEngine boogieEngine,
    CompilationInput input
    ) {
    this.options = options;
    Input = input;
    this.boogieEngine = boogieEngine;

    this.documentLoader = documentLoader;
    this.logger = logger;
    this.verifier = verifier;
    cancellationSource = new();
    cancellationSource.Token.Register(() => started.TrySetCanceled(cancellationSource.Token));

    verificationTickets.Enqueue(Unit.Default);
    MarkVerificationFinished();

    Program = ParseAsync();
    Resolution = ResolveAsync();
  }

  public void Start() {
    started.TrySetResult();
  }

  private async Task<Program> ParseAsync() {
    try {
      await started.Task;
      var uri = Input.Uri.ToUri();
      var errorReporter = new ObservableErrorReporter(options, uri);
      errorReporter.Updates.Subscribe(updates);
      staticDiagnosticsSubscription = errorReporter.Updates.Subscribe(newDiagnostic =>
        staticDiagnostics.GetOrAdd(newDiagnostic.Uri, _ => new()).Push(newDiagnostic.Diagnostic));
      transformedProgram = await documentLoader.ParseAsync(errorReporter, Input, cancellationSource.Token);

      var cloner = new Cloner(true, false);
      programAfterParsing = new Program(cloner, transformedProgram);

      var diagnosticsCopy = staticDiagnostics.ToImmutableDictionary(k => k.Key,
        kv => kv.Value.Select(d => d.ToLspDiagnostic()).ToImmutableList());
      updates.OnNext(new FinishedParsing(programAfterParsing, diagnosticsCopy));
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
      await Program;
      var resolution = await documentLoader.ResolveAsync(Input, transformedProgram!, cancellationSource.Token);

      updates.OnNext(new FinishedResolution(
        staticDiagnostics.ToImmutableDictionary(k => k.Key,
          kv => kv.Value.Select(d => d.ToLspDiagnostic()).ToImmutableList()),
        transformedProgram!,
        resolution.SymbolTable,
        resolution.SignatureAndCompletionTable,
        resolution.GhostRanges,
        resolution.CanVerifies));
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

  public static string GetImplementationName(Implementation implementation) {
    var prefix = implementation.Name.Split(BoogieGenerator.NameSeparator)[0];

    // Refining declarations get the token of what they're refining, so to distinguish them we need to
    // add the refining module name to the prefix.
    if (implementation.tok is RefinementToken refinementToken) {
      prefix += "." + refinementToken.InheritingModule.Name;
    }

    return prefix;
  }

  private int runningVerificationJobs;

  // When verifying a symbol, a ticket must be acquired before the SMT part of verification may start.
  private readonly AsyncQueue<Unit> verificationTickets = new();
  public async Task<bool> VerifySymbol(FilePosition verifiableLocation, bool onlyPrepareVerificationForGutterTests = false) {
    cancellationSource.Token.ThrowIfCancellationRequested();

    var resolution = await Resolution;
    if (resolution.ResolvedProgram.Reporter.HasErrorsUntilResolver) {
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

    var containingModule = canVerify.ContainingModule;
    if (!containingModule.ShouldVerify(resolution.ResolvedProgram.Compilation)) {
      return false;
    }

    if (!onlyPrepareVerificationForGutterTests && !verifyingOrVerifiedSymbols.TryAdd(canVerify, Unit.Default)) {
      return false;
    }
    updates.OnNext(new ScheduledVerification(canVerify));

    if (onlyPrepareVerificationForGutterTests) {
      await VerifyUnverifiedSymbol(onlyPrepareVerificationForGutterTests, canVerify, resolution);
      return true;
    }

    _ = VerifyUnverifiedSymbol(onlyPrepareVerificationForGutterTests, canVerify, resolution);
    return true;
  }

  private async Task VerifyUnverifiedSymbol(bool onlyPrepareVerificationForGutterTests, ICanVerify canVerify,
    ResolutionResult resolution) {
    try {

      var ticket = verificationTickets.Dequeue(CancellationToken.None);
      var containingModule = canVerify.ContainingModule;

      IncrementJobs();

      IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>> tasksForModule;
      try {
        tasksForModule = await translatedModules.GetOrAdd(containingModule, async () => {
          var result = await verifier.GetVerificationTasksAsync(boogieEngine, resolution, containingModule,
            cancellationSource.Token);
          foreach (var task in result) {
            cancellationSource.Token.Register(task.Cancel);
          }

          return result.GroupBy(t => ((IToken)t.Implementation.tok).GetFilePosition()).ToDictionary(
            g => g.Key,
            g => (IReadOnlyList<IImplementationTask>)g.ToList());
        });
      } catch (OperationCanceledException) {
        verificationCompleted.TrySetCanceled();
        throw;
      } catch (Exception e) {
        verificationCompleted.TrySetException(e);
        updates.OnNext(new InternalCompilationException(e));
        throw;
      }

      // For updated to be reliable, ImplementationsPerVerifiable must be Lazy
      var updated = false;
      var implementationTasksByName = implementationsPerVerifiable.GetOrAdd(canVerify, () => {
        var tasksForVerifiable =
          tasksForModule.GetValueOrDefault(canVerify.NameToken.GetFilePosition()) ??
          new List<IImplementationTask>(0);

        updated = true;
        return tasksForVerifiable.ToDictionary(
          t => GetImplementationName(t.Implementation),
          t => t);
      });
      if (updated) {
        updates.OnNext(new CanVerifyPartsIdentified(canVerify,
          implementationsPerVerifiable[canVerify].Values.ToList()));
      }

      // When multiple calls to VerifyUnverifiedSymbol are made, the order in which they pass this await matches the call order.
      await ticket;

      if (!onlyPrepareVerificationForGutterTests) {
        foreach (var task in implementationTasksByName.Values) {
          VerifyTask(canVerify, task);
        }
      }

      DecrementJobs();
    }
    finally {
      verificationTickets.Enqueue(Unit.Default);
    }
  }

  private void VerifyTask(ICanVerify canVerify, IImplementationTask task) {
    var statusUpdates = task.TryRun();
    if (statusUpdates == null) {
      if (task.CacheStatus is Completed completedCache) {
        foreach (var result in completedCache.Result.VCResults) {
          updates.OnNext(new BoogieUpdate(canVerify,
            task,
#pragma warning disable CS8625 // Cannot convert null literal to non-nullable reference type.
            new BatchCompleted(null /* unused */, result)));
#pragma warning restore CS8625 // Cannot convert null literal to non-nullable reference type.
        }

        updates.OnNext(new BoogieUpdate(canVerify,
          task,
          completedCache));
      }

      StatusUpdateHandlerFinally();
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
        if (e is not OperationCanceledException) {
          logger.LogError(e, $"Caught error in statusUpdates observable.");
        }

        StatusUpdateHandlerFinally();
      },
      StatusUpdateHandlerFinally
    );
  }

  private void StatusUpdateHandlerFinally() {
    try {
      var remainingJobs = Interlocked.Decrement(ref runningVerificationJobs);
      logger.LogDebug(
        $"StatusUpdateHandlerFinally called, remaining jobs {remainingJobs}, {Input.Uri} version {Input.Version}, " +
        $"startingCompilation.version {Input.Version}.");
      if (remainingJobs == 0) {
        MarkVerificationFinished();
      }
    } catch (Exception e) {
      logger.LogCritical(e, "Caught exception while handling finally code of statusUpdates handler.");
    }
  }

  public async Task Cancel(FilePosition filePosition) {
    var resolution = await Resolution;
    var canVerify = resolution.ResolvedProgram.FindNode<ICanVerify>(filePosition.Uri, filePosition.Position.ToDafnyPosition());
    if (canVerify != null) {
      var implementations = implementationsPerVerifiable.TryGetValue(canVerify, out var implementationsPerName)
        ? implementationsPerName!.Values : Enumerable.Empty<IImplementationTask>();
      foreach (var view in implementations) {
        view.Cancel();
      }
      verifyingOrVerifiedSymbols.TryRemove(canVerify, out _);
    }
  }

  public void IncrementJobs() {
    MarkVerificationStarted();
    var verifyTaskIncrementedJobs = Interlocked.Increment(ref runningVerificationJobs);
    logger.LogDebug($"Incremented jobs for verifyTask, remaining jobs {verifyTaskIncrementedJobs}, {Input.Uri} version {Input.Version}");
  }

  public void DecrementJobs() {
    var remainingJobs = Interlocked.Decrement(ref runningVerificationJobs);
    logger.LogDebug($"Decremented jobs, remaining jobs {remainingJobs}, {Input.Uri} version {Input.Version}");
    if (remainingJobs == 0) {
      logger.LogDebug($"Calling MarkVerificationFinished because there are no remaining verification jobs for {Input.Uri}, version {Input.Version}.");
      MarkVerificationFinished();
    }
  }

  private void HandleStatusUpdate(ICanVerify canVerify, IImplementationTask implementationTask, IVerificationStatus boogieStatus) {

    var tokenString = BoogieGenerator.ToDafnyToken(true, implementationTask.Implementation.tok).TokenToString(options);
    logger.LogDebug($"Received Boogie status {boogieStatus} for {tokenString}, version {Input.Version}");

    if (boogieStatus is Completed completed) {
      ReportVacuityAndRedundantAssumptionsChecks(implementationTask.Implementation, completed.Result);
    }

    updates.OnNext(new BoogieUpdate(canVerify,
      implementationTask,
      boogieStatus));
  }

  private void ReportVacuityAndRedundantAssumptionsChecks(
    Implementation implementation, VerificationResult verificationResult) {
    if (!Input.Options.Get(CommonOptionBag.WarnContradictoryAssumptions)
        && !Input.Options.Get(CommonOptionBag.WarnRedundantAssumptions)
       ) {
      return;
    }

    ProofDependencyWarnings.WarnAboutSuspiciousDependenciesForImplementation(Input.Options, transformedProgram!.Reporter,
      transformedProgram.ProofDependencyManager,
      new DafnyConsolePrinter.ImplementationLogEntry(implementation.VerboseName, implementation.tok),
      DafnyConsolePrinter.DistillVerificationResult(verificationResult));
  }

  public void CancelPendingUpdates() {
    cancellationSource.Cancel();
  }

  private void MarkVerificationStarted() {
    logger.LogDebug($"MarkVerificationStarted called for {Input.Uri} version {Input.Version}");
    if (verificationCompleted.Task.IsCompleted) {
      verificationCompleted = new TaskCompletionSource();
    }
  }

  private void MarkVerificationFinished() {
    logger.LogDebug($"MarkVerificationFinished called for {Input.Uri} version {Input.Version}");
    verificationCompleted.TrySetResult();
  }

  public Task Finished {
    get {
      logger.LogDebug($"LastDocument {Input.Uri} will return document version {Input.Version}");
      return Resolution.ContinueWith(
        t => {
          if (t.IsCompletedSuccessfully) {
#pragma warning disable VSTHRD103
            return verificationCompleted.Task.ContinueWith(
              verificationCompletedTask => {
                logger.LogDebug(
                  $"LastDocument returning translated compilation {Input.Uri} with status {verificationCompletedTask.Status}");
                return Task.CompletedTask;
              }, TaskScheduler.Current).Unwrap();
#pragma warning restore VSTHRD103
          }

          return Program;
        }, TaskScheduler.Current).Unwrap();
    }
  }

  public async Task<TextEditContainer?> GetTextEditToFormatCode(Uri uri) {
    // TODO https://github.com/dafny-lang/dafny/issues/3416
    var program = await Program;

    if (program.Reporter.HasErrors) {
      return null;
    }

    var firstToken = program.GetFirstTokenForUri(uri);
    if (firstToken == null) {
      return null;
    }
    var result = Formatting.__default.ReindentProgramFromFirstToken(firstToken,
      IndentationFormatter.ForProgram(program));

    var lastToken = firstToken;
    while (lastToken.Next != null) {
      lastToken = lastToken.Next;
    }
    // TODO: end position doesn't take into account trailing trivia: https://github.com/dafny-lang/dafny/issues/3415
    return new TextEditContainer(new TextEdit[] {
      new() {NewText = result, Range = new Range(new Position(0,0), lastToken.GetLspPosition())}
    });

  }

  private bool disposed;

  public void Dispose() {
    if (disposed) {
      return;
    }

    disposed = true;
    CancelPendingUpdates();
  }
}
