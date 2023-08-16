using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Text document loader implementation that offloads the whole load procedure on one dedicated
  /// thread with a stack size of 256MB. Since only one thread is used, document loading is implicitely synchronized.
  /// The verification runs on the calling thread.
  /// </summary>
  /// <remarks>
  /// The increased stack size is necessary to solve the issue https://github.com/dafny-lang/dafny/issues/1447.
  /// </remarks>
  public class TextDocumentLoader : ITextDocumentLoader {
    private readonly ILogger<ITextDocumentLoader> logger;
    private readonly IDafnyParser parser;
    private readonly IGhostStateDiagnosticCollector ghostStateDiagnosticCollector;
    protected readonly ICompilationStatusNotificationPublisher statusPublisher;
    private readonly ILogger<CachingResolver> innerLogger;
    private readonly SemaphoreSlim resolverMutex = new(1);
    private readonly ITelemetryPublisher telemetryPublisher;

    public TextDocumentLoader(
      ILogger<ITextDocumentLoader> logger,
      IDafnyParser parser,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher statusPublisher,
      ILogger<CachingResolver> innerLogger,
      ITelemetryPublisher telemetryPublisher) {
      this.logger = logger;
      this.parser = parser;
      this.ghostStateDiagnosticCollector = ghostStateDiagnosticCollector;
      this.statusPublisher = statusPublisher;
      this.innerLogger = innerLogger;
      this.telemetryPublisher = telemetryPublisher;
    }

    public IdeState CreateUnloaded(Compilation compilation) {
      return CreateDocumentWithEmptySymbolTable(compilation, ImmutableDictionary<Uri, IReadOnlyList<Diagnostic>>.Empty);
    }

    public async Task<CompilationAfterParsing> ParseAsync(DafnyOptions options, Compilation compilation,
      IReadOnlyDictionary<Uri, VerificationTree> migratedVerificationTrees, CancellationToken cancellationToken) {
#pragma warning disable CS1998
      return await await DafnyMain.LargeStackFactory.StartNew(
        async () => ParseInternal(options, compilation, migratedVerificationTrees, cancellationToken), cancellationToken
#pragma warning restore CS1998
      );
    }

    private CompilationAfterParsing ParseInternal(DafnyOptions options, Compilation compilation,
      IReadOnlyDictionary<Uri, VerificationTree> migratedVerificationTrees,
      CancellationToken cancellationToken) {
      var project = compilation.Project;
      var errorReporter = new DiagnosticErrorReporter(options, project.Uri);
      _ = statusPublisher.SendStatusNotification(compilation, CompilationStatus.Parsing);
      var program = parser.Parse(compilation, errorReporter, cancellationToken);
      var compilationAfterParsing = new CompilationAfterParsing(compilation, program, errorReporter.AllDiagnosticsCopy,
        compilation.RootUris.ToDictionary(uri => uri,
          uri => migratedVerificationTrees.GetValueOrDefault(uri) ?? new DocumentVerificationTree(program, uri)));
      if (errorReporter.HasErrors) {
        _ = statusPublisher.SendStatusNotification(compilation, CompilationStatus.ParsingFailed);
        return compilationAfterParsing;
      }

      return compilationAfterParsing;
    }

    public async Task<CompilationAfterResolution> ResolveAsync(DafnyOptions options,
      CompilationAfterParsing compilation,
      IReadOnlyDictionary<Uri, VerificationTree> migratedVerificationTrees,
      CancellationToken cancellationToken) {
#pragma warning disable CS1998
      return await await DafnyMain.LargeStackFactory.StartNew(
        async () => ResolveInternal(compilation, migratedVerificationTrees, cancellationToken), cancellationToken
#pragma warning restore CS1998
        );
    }

    private CompilationAfterResolution ResolveInternal(CompilationAfterParsing compilation,
      IReadOnlyDictionary<Uri, VerificationTree> migratedVerificationTrees, CancellationToken cancellationToken) {

      var program = compilation.Program;
      var errorReporter = (DiagnosticErrorReporter)program.Reporter;
      if (errorReporter.HasErrors) {
        throw new TaskCanceledException();
      }

      _ = statusPublisher.SendStatusNotification(compilation, CompilationStatus.ResolutionStarted);
      ResolveSymbols(compilation.Project, program, cancellationToken);
      var newSymbolTable = errorReporter.HasErrors
        ? null
        : SymbolTable.CreateFrom(program, compilation, cancellationToken);
      _ = statusPublisher.SendStatusNotification(compilation, errorReporter.HasErrors ? CompilationStatus.ResolutionFailed : CompilationStatus.CompilationSucceeded);

      var ghostDiagnostics = ghostStateDiagnosticCollector.GetGhostStateDiagnostics(program, cancellationToken);

      List<ICanVerify> verifiables;
      if (errorReporter.HasErrorsUntilResolver) {
        verifiables = new();
      } else {
        var symbols = SymbolExtensions.GetSymbolDescendants(program.DefaultModule);
        verifiables = symbols.OfType<ICanVerify>().Where(v => !AutoGeneratedToken.Is(v.RangeToken) &&
                                                              v.ContainingModule.ShouldVerify(program.Compilation) &&
                                                              v.ShouldVerify(program.Compilation) &&
                                                              v.ShouldVerify).ToList();
      }

      return new CompilationAfterResolution(compilation,
        errorReporter.AllDiagnosticsCopy,
        newSymbolTable,
        ghostDiagnostics,
        verifiables,
        new(),
        new()
      );
    }

    private readonly ResolutionCache resolutionCache = new();

    public void ResolveSymbols(DafnyProject project, Program program, CancellationToken cancellationToken) {
      // TODO The resolution requires mutual exclusion since it sets static variables of classes like Microsoft.Dafny.Type.
      //      Although, the variables are marked "ThreadStatic" - thus it might not be necessary. But there might be
      //      other classes as well.
      resolverMutex.Wait(cancellationToken);
      try {
        RunDafnyResolver(project, program, cancellationToken);
      }
      finally {
        resolverMutex.Release();
      }
    }

    private void RunDafnyResolver(DafnyProject project, Program program, CancellationToken cancellationToken) {
      var beforeResolution = DateTime.Now;
      try {
        var resolver = program.Options.Get(ServerCommand.UseCaching)
          ? new CachingResolver(program, innerLogger, telemetryPublisher, resolutionCache)
          : new ProgramResolver(program);
        resolver.Resolve(cancellationToken);
        int resolverErrors = resolver.Reporter.ErrorCountUntilResolver;
        if (resolverErrors > 0) {
          logger.LogDebug("encountered {ErrorCount} errors while resolving {DocumentUri}", resolverErrors,
          project.Uri);
        }
      }
      finally {
        telemetryPublisher.PublishTime("Resolution", project.Uri.ToString(), DateTime.Now - beforeResolution);
      }
    }

    private IdeState CreateDocumentWithEmptySymbolTable(Compilation compilation,
      IReadOnlyDictionary<Uri, IReadOnlyList<Diagnostic>> resolutionDiagnostics) {
      var program = new EmptyNode();
      return new IdeState(
        compilation.Version,
        compilation,
        program,
        resolutionDiagnostics,
        SymbolTable.Empty(),
        new(),
        Array.Empty<Counterexample>(),
        ImmutableDictionary<Uri, IReadOnlyList<Range>>.Empty,
      ImmutableDictionary<Uri, VerificationTree>.Empty
      );
    }
  }
}
