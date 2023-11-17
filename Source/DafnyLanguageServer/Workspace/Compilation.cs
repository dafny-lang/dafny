using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Reactive;
using System.Reactive.Disposables;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public delegate Compilation CreateCompilation(
  ExecutionEngine boogieEngine,
  CompilationInput compilation);

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

  private DafnyOptions Options => Input.Options;
  public CompilationInput Input { get; }
  public DafnyProject Project => Input.Project;
  private readonly ExecutionEngine boogieEngine;

  private readonly Subject<ICompilationEvent> updates = new();
  public IObservable<ICompilationEvent> Updates => updates;

  private Program? programAfterParsing;
  private Program? transformedProgram;
  private readonly IDisposable staticDiagnosticsSubscription;

  public Task<Program> Program { get; }
  public Task<ResolutionResult> Resolution { get; }

  public ErrorReporter Reporter => errorReporter;

  public IReadOnlyList<DafnyFile>? RootFiles { get; set; }

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
    staticDiagnosticsSubscription = errorReporter.Updates.Subscribe(newDiagnostic =>
      staticDiagnostics.GetOrAdd(newDiagnostic.Uri, _ => new()).Push(newDiagnostic.Diagnostic));

    cancellationSource = new();
    cancellationSource.Token.Register(() => started.TrySetCanceled(cancellationSource.Token));

    verificationTickets.Enqueue(Unit.Default);

    Program = ParseAsync();
    Resolution = ResolveAsync();
  }

  public void Start() {
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
      var file = DafnyFile.CreateAndValidate(errorReporter, fileSystem, Options, uri, Token.Cli);
      if (file != null) {
        result.Add(file);
      }
    }

    if (Options.Get(CommonOptionBag.UseStandardLibraries)) {
      if (Options.CompilerName is null or "cs" or "java" or "go" or "py" or "js") {
        var targetName = Options.CompilerName ?? "notarget";
        var stdlibDooUri = new Uri($"{DafnyMain.StandardLibrariesDooUriBase}-{targetName}.doo");
        Options.CliRootSourceUris.Add(stdlibDooUri);
        result.Add(DafnyFile.CreateAndValidate(errorReporter, OnDiskFileSystem.Instance, Options, stdlibDooUri, Project.StartingToken));
      }

      result.Add(DafnyFile.CreateAndValidate(errorReporter, fileSystem, Options, DafnyMain.StandardLibrariesDooUri, Project.StartingToken));
      result.Add(DafnyFile.CreateAndValidate(errorReporter, fileSystem, Options, DafnyMain.StandardLibrariesArithmeticDooUri, Project.StartingToken));
    }

    foreach (var library in Options.Get(CommonOptionBag.Libraries)) {
      var file = DafnyFile.CreateAndValidate(errorReporter, fileSystem, Options, new Uri(library.FullName), Project.StartingToken);
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
        errorReporter.Info(MessageSource.Parser, Project.StartingToken, "Files referenced by project are:" + Environment.NewLine + filesMessage);
      } else {
        errorReporter.Warning(MessageSource.Parser, CompilerErrors.ErrorId.None, Project.StartingToken, "Project references no files");
      }
    }

    return result;
  }

  private async Task<Program> ParseAsync() {
    try {
      await started.Task;
      transformedProgram = await documentLoader.ParseAsync(this, cancellationSource.Token);

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
        throw;
      } catch (Exception e) {
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

      }
    );
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

  private void HandleStatusUpdate(ICanVerify canVerify, IImplementationTask implementationTask, IVerificationStatus boogieStatus) {
    var tokenString = BoogieGenerator.ToDafnyToken(true, implementationTask.Implementation.tok).TokenToString(Options);
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
  private readonly ObservableErrorReporter errorReporter;

  public void Dispose() {
    if (disposed) {
      return;
    }

    disposed = true;
    CancelPendingUpdates();
  }
}
