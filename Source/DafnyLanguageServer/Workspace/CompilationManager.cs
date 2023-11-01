using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Reactive;
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

public delegate CompilationManager CreateCompilationManager(
  DafnyOptions options,
  ExecutionEngine boogieEngine,
  Compilation compilation,
  IReadOnlyDictionary<Uri, DocumentVerificationTree> migratedVerificationTrees);

/// <summary>
/// The compilation of a single document version.
/// The document will be parsed, resolved, translated to Boogie and verified.
///
/// Compilation may be configured to pause after translation,
/// requiring a call to CompilationManager.Verify for the document to be verified.
///
/// Compilation is agnostic to document updates, it does not handle the migration of old document state.
/// </summary>
public class CompilationManager : IDisposable {

  private readonly ILogger logger;
  private readonly ITextDocumentLoader documentLoader;
  private readonly IProgramVerifier verifier;

  // TODO CompilationManager shouldn't be aware of migration
  private readonly IReadOnlyDictionary<Uri, DocumentVerificationTree> migratedVerificationTrees;

  private readonly TaskCompletionSource started = new();
  private readonly CancellationTokenSource cancellationSource;
  private readonly ConcurrentDictionary<Uri, ConcurrentStack<DafnyDiagnostic>> diagnostics = new();
  public DafnyDiagnostic[] GetDiagnosticsForUri(Uri uri) =>
    diagnostics.TryGetValue(uri, out var forUri) ? forUri.ToArray() : Array.Empty<DafnyDiagnostic>();

  private TaskCompletionSource verificationCompleted = new();
  private readonly DafnyOptions options;
  public Compilation StartingCompilation { get; }
  private readonly ExecutionEngine boogieEngine;

  private readonly Subject<ICompilationEvent> compilationUpdates = new();
  public IObservable<ICompilationEvent> CompilationUpdates => compilationUpdates;

  public Task<CompilationAfterParsing> ParsedCompilation { get; }
  public Task<CompilationAfterResolution> ResolvedCompilation { get; }

  public CompilationManager(
    ILogger<CompilationManager> logger,
    ITextDocumentLoader documentLoader,
    IProgramVerifier verifier,
    DafnyOptions options,
    ExecutionEngine boogieEngine,
    Compilation compilation,
    IReadOnlyDictionary<Uri, DocumentVerificationTree> migratedVerificationTrees
    ) {
    this.options = options;
    StartingCompilation = compilation;
    this.boogieEngine = boogieEngine;
    this.migratedVerificationTrees = migratedVerificationTrees;

    this.documentLoader = documentLoader;
    this.logger = logger;
    this.verifier = verifier;
    cancellationSource = new();
    cancellationSource.Token.Register(() => started.TrySetCanceled(cancellationSource.Token));

    verificationTickets.Enqueue(Unit.Default);
    MarkVerificationFinished();

    ParsedCompilation = ParseAsync();
    ResolvedCompilation = ResolveAsync();
  }

  public void Start() {
    started.TrySetResult();
  }

  private async Task<CompilationAfterParsing> ParseAsync() {
    try {
      await started.Task;
      var uri = StartingCompilation.Uri.ToUri();
      var errorReporter = new ObservableErrorReporter(options, uri);
      errorReporter.Updates.Subscribe(compilationUpdates);
      errorReporter.Updates.Subscribe(onNext => diagnostics.GetOrAdd(uri, _ => new()).Push(onNext.Diagnostic));
      var parsedCompilation = await documentLoader.ParseAsync(errorReporter, StartingCompilation, migratedVerificationTrees,
        cancellationSource.Token);

      compilationUpdates.OnNext(new FinishedParsing(parsedCompilation));
      logger.LogDebug(
        $"Passed parsedCompilation to documentUpdates.OnNext, resolving ParsedCompilation task for version {parsedCompilation.Version}.");
      return parsedCompilation;

    } catch (OperationCanceledException) {
      throw;
    } catch (Exception e) {
      compilationUpdates.OnError(e);
      throw;
    }
  }

  private async Task<CompilationAfterResolution> ResolveAsync() {
    try {
      var parsedCompilation = await ParsedCompilation;
      var resolvedCompilation = await documentLoader.ResolveAsync(options, parsedCompilation, cancellationSource.Token);

      compilationUpdates.OnNext(new FinishedResolution(
        resolvedCompilation,
        resolvedCompilation.SymbolTable,
        resolvedCompilation.SignatureAndCompletionTable,
        resolvedCompilation.GhostDiagnostics,
        resolvedCompilation.CanVerifies));
      logger.LogDebug($"Passed resolvedCompilation to documentUpdates.OnNext, resolving ResolvedCompilation task for version {resolvedCompilation.Version}.");
      return resolvedCompilation;

    } catch (OperationCanceledException) {
      throw;
    } catch (Exception e) {
      compilationUpdates.OnError(e);
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

    var compilation = await ResolvedCompilation;
    if (compilation.Program.Reporter.HasErrorsUntilResolver) {
      throw new TaskCanceledException();
    }

    var canVerify = compilation.Program.FindNode(verifiableLocation.Uri, verifiableLocation.Position.ToDafnyPosition(),
      node => {
        if (node is not ICanVerify) {
          return false;
        }
        // Sometimes traversing the AST can return different versions of a single source AST node,
        // for example in the case of a LeastLemma, which is later also represented as a PrefixLemma.
        // This check ensures that we consistently use the same version of an AST node. 
        return compilation.CanVerifies!.Contains(node);
      }) as ICanVerify;

    if (canVerify == null) {
      return false;
    }

    var containingModule = canVerify.ContainingModule;
    if (!containingModule.ShouldVerify(compilation.Program.Compilation)) {
      return false;
    }

    if (!onlyPrepareVerificationForGutterTests && !compilation.VerifyingOrVerifiedSymbols.TryAdd(canVerify, Unit.Default)) {
      return false;
    }
    compilationUpdates.OnNext(new ScheduledVerification(canVerify));

    if (onlyPrepareVerificationForGutterTests) {
      await VerifyUnverifiedSymbol(onlyPrepareVerificationForGutterTests, canVerify, compilation);
      return true;
    }

    _ = VerifyUnverifiedSymbol(onlyPrepareVerificationForGutterTests, canVerify, compilation);
    return true;
  }

  private async Task VerifyUnverifiedSymbol(bool onlyPrepareVerificationForGutterTests, ICanVerify canVerify,
    CompilationAfterResolution compilation) {
    try {

      var ticket = verificationTickets.Dequeue(CancellationToken.None);
      var containingModule = canVerify.ContainingModule;

      IncrementJobs();

      IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>> tasksForModule;
      try {
        tasksForModule = await compilation.TranslatedModules.GetOrAdd(containingModule, async () => {
          var result = await verifier.GetVerificationTasksAsync(boogieEngine, compilation, containingModule,
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
        compilationUpdates.OnError(e);
        throw;
      }

      // For updated to be reliable, ImplementationsPerVerifiable must be Lazy
      var updated = false;
      var implementations = compilation.ImplementationsPerVerifiable.GetOrAdd(canVerify, () => {
        var tasksForVerifiable =
          tasksForModule.GetValueOrDefault(canVerify.NameToken.GetFilePosition()) ??
          new List<IImplementationTask>(0);

        updated = true;
        return tasksForVerifiable.ToDictionary(
          t => GetImplementationName(t.Implementation),
          t => new ImplementationState(t, PublishedVerificationStatus.Stale, Array.Empty<DafnyDiagnostic>(), false));
      });
      if (updated) {
        compilationUpdates.OnNext(new CanVerifyPartsIdentified(canVerify, 
          compilation.ImplementationsPerVerifiable[canVerify].Values.Select(s => s.Task).ToList()));
      }

      // When multiple calls to VerifyUnverifiedSymbol are made, the order in which they pass this await matches the call order.
      await ticket;

      if (!onlyPrepareVerificationForGutterTests) {
        var tasks = implementations.Values.Select(t => t.Task).ToList();

        foreach (var task in tasks) {
          var statusUpdates = task.TryRun();
          if (statusUpdates == null) {
            if (task.CacheStatus is Completed completedCache) {
              foreach (var result in completedCache.Result.VCResults) {
                compilationUpdates.OnNext(new BoogieUpdate(canVerify,
                  task,
                  new BatchCompleted(null /* unused */, result)));
              }

              compilationUpdates.OnNext(new BoogieUpdate(canVerify,
                task,
                completedCache));
            }

            StatusUpdateHandlerFinally();
            return;
          }

          var incrementedJobs = Interlocked.Increment(ref runningVerificationJobs);
          logger.LogDebug(
            $"Incremented jobs for task, remaining jobs {incrementedJobs}, {compilation.Uri} version {compilation.Version}");

          statusUpdates.Subscribe(
            update => {
              try {
                HandleStatusUpdate(compilation, canVerify, task, update);
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

        void StatusUpdateHandlerFinally() {
          try {
            var remainingJobs = Interlocked.Decrement(ref runningVerificationJobs);
            logger.LogDebug(
              $"StatusUpdateHandlerFinally called, remaining jobs {remainingJobs}, {compilation.Uri} version {compilation.Version}, " +
              $"startingCompilation.version {StartingCompilation.Version}.");
            if (remainingJobs == 0) {
              FinishedNotifications(compilation, canVerify);
            }
          } catch (Exception e) {
            logger.LogCritical(e, "Caught exception while handling finally code of statusUpdates handler.");
          }
        }
      }

      DecrementJobs();
    }
    finally {
      verificationTickets.Enqueue(Unit.Default);
    }
  }

  public async Task Cancel(FilePosition filePosition) {
    var resolvedCompilation = await ResolvedCompilation;
    var canVerify = resolvedCompilation.Program.FindNode<ICanVerify>(filePosition.Uri, filePosition.Position.ToDafnyPosition());
    if (canVerify != null) {
      var implementations = resolvedCompilation.ImplementationsPerVerifiable.TryGetValue(canVerify, out var implementationsPerName)
        ? implementationsPerName!.Values : Enumerable.Empty<ImplementationState>();
      foreach (var view in implementations) {
        view.Task.Cancel();
      }
      resolvedCompilation.VerifyingOrVerifiedSymbols.TryRemove(canVerify, out _);
    }
  }

  public void IncrementJobs() {
    MarkVerificationStarted();
    var verifyTaskIncrementedJobs = Interlocked.Increment(ref runningVerificationJobs);
    logger.LogDebug($"Incremented jobs for verifyTask, remaining jobs {verifyTaskIncrementedJobs}, {StartingCompilation.Uri} version {StartingCompilation.Version}");
  }

  public void DecrementJobs() {
    var remainingJobs = Interlocked.Decrement(ref runningVerificationJobs);
    logger.LogDebug($"Decremented jobs, remaining jobs {remainingJobs}, {StartingCompilation.Uri} version {StartingCompilation.Version}");
    if (remainingJobs == 0) {
      logger.LogDebug($"Calling MarkVerificationFinished because there are no remaining verification jobs for {StartingCompilation.Uri}, version {StartingCompilation.Version}.");
      MarkVerificationFinished();
    }
  }

  private void FinishedNotifications(CompilationAfterResolution compilation, ICanVerify canVerify) {
    if (ReportGutterStatus) {
      if (!cancellationSource.IsCancellationRequested) {
        // All unvisited trees need to set them as "verified"
        new GutterIconAndHoverVerificationDetailsManager(logger).SetAllUnvisitedMethodsAsVerified(compilation, canVerify);
      }
    }

    MarkVerificationFinished();
  }

  private void HandleStatusUpdate(CompilationAfterResolution compilation, ICanVerify canVerify, IImplementationTask implementationTask, IVerificationStatus boogieStatus) {

    var tokenString = BoogieGenerator.ToDafnyToken(true, implementationTask.Implementation.tok).TokenToString(options);
    logger.LogDebug($"Received status {boogieStatus} for {tokenString}, version {compilation.Version}");

    if (boogieStatus is Completed completed) {
      ReportVacuityAndRedundantAssumptionsChecks(compilation, implementationTask.Implementation, completed.Result);
    }
    
    compilationUpdates.OnNext(new BoogieUpdate(canVerify,
      implementationTask,
      boogieStatus));
  }

  private bool ReportGutterStatus => options.Get(GutterIconAndHoverVerificationDetailsManager.LineVerificationStatus);

  private static void ReportVacuityAndRedundantAssumptionsChecks(CompilationAfterResolution compilation,
    Implementation implementation, VerificationResult verificationResult) {
    var options = compilation.Program.Reporter.Options;
    if (!options.Get(CommonOptionBag.WarnContradictoryAssumptions)
        && !options.Get(CommonOptionBag.WarnRedundantAssumptions)
       ) {
      return;
    }

    ProofDependencyWarnings.WarnAboutSuspiciousDependenciesForImplementation(options, compilation.Program.Reporter,
      compilation.Program.ProofDependencyManager,
      new DafnyConsolePrinter.ImplementationLogEntry(implementation.VerboseName, implementation.tok),
      DafnyConsolePrinter.DistillVerificationResult(verificationResult));
  }

  public void CancelPendingUpdates() {
    cancellationSource.Cancel();
  }

  private void MarkVerificationStarted() {
    logger.LogDebug($"MarkVerificationStarted called for {StartingCompilation.Uri} version {StartingCompilation.Version}");
    if (verificationCompleted.Task.IsCompleted) {
      verificationCompleted = new TaskCompletionSource();
    }
  }

  private void MarkVerificationFinished() {
    logger.LogDebug($"MarkVerificationFinished called for {StartingCompilation.Uri} version {StartingCompilation.Version}");
    verificationCompleted.TrySetResult();
  }

  public Task<CompilationAfterParsing> LastDocument {
    get {
      logger.LogDebug($"LastDocument {StartingCompilation.Uri} will return document version {StartingCompilation.Version}");
      return ResolvedCompilation.ContinueWith(
        t => {
          if (t.IsCompletedSuccessfully) {
#pragma warning disable VSTHRD103
            return verificationCompleted.Task.ContinueWith(
              verificationCompletedTask => {
                logger.LogDebug(
                  $"LastDocument returning translated compilation {StartingCompilation.Uri} with status {verificationCompletedTask.Status}");
                return Task.FromResult<CompilationAfterParsing>(t.Result);
              }, TaskScheduler.Current).Unwrap();
#pragma warning restore VSTHRD103
          }

          return ParsedCompilation;
        }, TaskScheduler.Current).Unwrap();
    }
  }

  public async Task<TextEditContainer?> GetTextEditToFormatCode(Uri uri) {
    // TODO https://github.com/dafny-lang/dafny/issues/3416
    var parsedDocument = await ParsedCompilation;

    if (parsedDocument.Program.Reporter.HasErrors) {
      return null;
    }

    var firstToken = parsedDocument.Program.GetFirstTokenForUri(uri);
    if (firstToken == null) {
      return null;
    }
    var result = Formatting.__default.ReindentProgramFromFirstToken(firstToken,
      IndentationFormatter.ForProgram(parsedDocument.Program));

    var lastToken = firstToken;
    while (lastToken.Next != null) {
      lastToken = lastToken.Next;
    }
    // TODO: https://github.com/dafny-lang/dafny/issues/3415
    return new TextEditContainer(new TextEdit[] {
      // TODO end position doesn't take into account trailing trivia
      new() {NewText = result, Range = new Range(new Position(0,0), lastToken.GetLspPosition())}
    });

  }

  private bool disposed = false;
  public void Dispose() {
    if (disposed) {
      return;
    }

    disposed = true;
    CancelPendingUpdates();
  }
}
