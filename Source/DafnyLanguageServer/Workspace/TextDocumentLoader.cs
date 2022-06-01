using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Reactive.Threading.Tasks;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using VC;
using VerificationStatus = Microsoft.Boogie.VerificationStatus;

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
    private VerifierOptions VerifierOptions { get; }
    private const int ResolverMaxStackSize = 0x10000000; // 256MB
    private static readonly ThreadTaskScheduler ResolverScheduler = new(ResolverMaxStackSize);

    private DafnyOptions Options => DafnyOptions.O;
    private readonly IDafnyParser parser;
    private readonly ISymbolResolver symbolResolver;
    private readonly ISymbolTableFactory symbolTableFactory;
    private readonly IProgramVerifier verifier;
    private readonly IGhostStateDiagnosticCollector ghostStateDiagnosticCollector;
    protected readonly ICompilationStatusNotificationPublisher notificationPublisher;
    protected readonly ILoggerFactory loggerFactory;
    private readonly ILogger<TextDocumentLoader> logger;
    protected readonly IDiagnosticPublisher diagnosticPublisher;

    protected TextDocumentLoader(
      ILoggerFactory loggerFactory,
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher notificationPublisher,
      IDiagnosticPublisher diagnosticPublisher,
      VerifierOptions verifierOptions) {
      VerifierOptions = verifierOptions;
      this.parser = parser;
      this.symbolResolver = symbolResolver;
      this.verifier = verifier;
      this.symbolTableFactory = symbolTableFactory;
      this.ghostStateDiagnosticCollector = ghostStateDiagnosticCollector;
      this.notificationPublisher = notificationPublisher;
      this.loggerFactory = loggerFactory;
      this.logger = loggerFactory.CreateLogger<TextDocumentLoader>();
      this.diagnosticPublisher = diagnosticPublisher;
    }

    public static TextDocumentLoader Create(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher notificationPublisher,
      ILoggerFactory loggerFactory,
      IDiagnosticPublisher diagnosticPublisher,
      VerifierOptions verifierOptions
      ) {
      return new TextDocumentLoader(loggerFactory, parser, symbolResolver, verifier, symbolTableFactory, ghostStateDiagnosticCollector, notificationPublisher, diagnosticPublisher, verifierOptions);
    }

    public DafnyDocument CreateUnloaded(DocumentTextBuffer textDocument, CancellationToken cancellationToken) {
      var errorReporter = new DiagnosticErrorReporter(textDocument.Uri);
      return CreateDocumentWithEmptySymbolTable(
        loggerFactory.CreateLogger<SymbolTable>(),
        textDocument,
        errorReporter,
        parser.CreateUnparsed(textDocument, errorReporter, cancellationToken),
        loadCanceled: true
      );
    }

    public async Task<DafnyDocument> PrepareVerificationTasksAsync(DafnyDocument loaded, CancellationToken cancellationToken) {
      if (loaded.ParseAndResolutionDiagnostics.Any(d => d.Severity == DiagnosticSeverity.Error)) {
        throw new TaskCanceledException();
      }

      var verificationTasks = await verifier.GetVerificationTasksAsync(loaded, cancellationToken);

      var initialViews = new Dictionary<ImplementationId, ImplementationView>();
      foreach (var task in verificationTasks.Tasks) {
        var status = await StatusFromImplementationTaskAsync(task);
        var view = new ImplementationView(task.Implementation.tok.GetLspRange(), status, Array.Empty<Diagnostic>());
        initialViews.Add(GetImplementationId(task.Implementation), view);
      }
      return loaded with {
        VerificationTasks = verificationTasks,
        ImplementationViews = initialViews,
      };
    }

    public async Task<DafnyDocument> LoadAsync(DocumentTextBuffer textDocument, CancellationToken cancellationToken) {
#pragma warning disable CS1998
      return await await Task.Factory.StartNew(async () => LoadInternal(textDocument, cancellationToken), cancellationToken,
#pragma warning restore CS1998
        TaskCreationOptions.None, ResolverScheduler);
    }

    private DafnyDocument LoadInternal(DocumentTextBuffer textDocument, CancellationToken cancellationToken) {
      var errorReporter = new DiagnosticErrorReporter(textDocument.Uri);
      var program = parser.Parse(textDocument, errorReporter, cancellationToken);
      IncludePluginLoadErrors(errorReporter, program);
      if (errorReporter.HasErrors) {
        notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.ParsingFailed);
        return CreateDocumentWithEmptySymbolTable(loggerFactory.CreateLogger<SymbolTable>(), textDocument, errorReporter, program, loadCanceled: false);
      }

      var compilationUnit = symbolResolver.ResolveSymbols(textDocument, program, cancellationToken);
      var symbolTable = symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      if (errorReporter.HasErrors) {
        notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.ResolutionFailed);
      } else {
        notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.CompilationSucceeded);
      }
      var ghostDiagnostics = ghostStateDiagnosticCollector.GetGhostStateDiagnostics(symbolTable, cancellationToken).ToArray();

      return new DafnyDocument(textDocument, errorReporter.GetDiagnostics(textDocument.Uri),
        new Dictionary<ImplementationId, ImplementationView>(),
        Array.Empty<Counterexample>(),
        ghostDiagnostics, program, symbolTable);
    }

    private static void IncludePluginLoadErrors(DiagnosticErrorReporter errorReporter, Dafny.Program program) {
      foreach (var error in DafnyLanguageServer.PluginLoadErrors) {
        errorReporter.Error(MessageSource.Compiler, program.GetFirstTopLevelToken(), error);
      }
    }

    private DafnyDocument CreateDocumentWithEmptySymbolTable(
      ILogger<SymbolTable> logger,
      DocumentTextBuffer textDocument,
      DiagnosticErrorReporter errorReporter,
      Dafny.Program program,
      bool loadCanceled
    ) {
      return new DafnyDocument(
        textDocument,
        errorReporter.GetDiagnostics(textDocument.Uri),
        new Dictionary<ImplementationId, ImplementationView>(),
        Array.Empty<Counterexample>(),
        Array.Empty<Diagnostic>(),
        program,
        CreateEmptySymbolTable(program, logger),
        null,
        loadCanceled
      );
    }

    private static SymbolTable CreateEmptySymbolTable(Dafny.Program program, ILogger<SymbolTable> logger) {
      return new SymbolTable(
        logger,
        new CompilationUnit(program),
        new Dictionary<object, ILocalizableSymbol>(),
        new Dictionary<ISymbol, SymbolLocation>(),
        new IntervalTree<Position, ILocalizableSymbol>(),
        symbolsResolved: false
      );
    }

    public IObservable<DafnyDocument> Verify(DafnyDocument document, CancellationToken cancellationToken) {
      notificationPublisher.SendStatusNotification(document.TextDocumentItem, CompilationStatus.VerificationStarted);

      var progressReporter = CreateVerificationProgressReporter(document);
      document.VerificationTasks!.BatchCompletions.Subscribe(progressReporter.ReportAssertionBatchResult);
      var implementationTasks = document.VerificationTasks!.Tasks;

      if (VerifierOptions.GutterStatus) {
        progressReporter.RecomputeVerificationTree();
        progressReporter.ReportRealtimeDiagnostics(false, document);
        progressReporter.ReportImplementationsBeforeVerification(
          implementationTasks.Select(t => t.Implementation).ToArray());
      }

      var result = GetVerifiedDafnyDocuments(document, implementationTasks, progressReporter);

      foreach (var implementationTask in implementationTasks) {
        cancellationToken.Register(implementationTask.Cancel);
        try {
          implementationTask.Run();
        } catch (InvalidOperationException) {
          // Thrown in case the task was already cancelled. Requires a Boogie fix to remove.
        }
        if (VerifierOptions.GutterStatus) {
          progressReporter.ReportStartVerifyImplementation(implementationTask.Implementation);
        }
      }

      if (VerifierOptions.GutterStatus) {
        ReportRealtimeDiagnostics(document, result, progressReporter, cancellationToken);
      }

      var _ = NotifyStatusAsync(document.TextDocumentItem, result.DefaultIfEmpty(document), cancellationToken);
      return result;
    }

    private IObservable<DafnyDocument> GetVerifiedDafnyDocuments(DafnyDocument document, IReadOnlyList<IImplementationTask> implementationTasks,
      VerificationProgressReporter progressReporter) {

      var implementationViews = GetExistingViews(document, implementationTasks);
      var counterExamples = new ConcurrentStack<Counterexample>();

      var implementationsUpdates = implementationTasks.Select(implementationTask =>
        implementationTask.ObservableStatus.SelectMany(boogieStatus =>
          HandleStatusUpdate(implementationTask, boogieStatus).ToObservable()));
      var result = implementationsUpdates.Merge().Replay();
      result.Connect();
      return result;


      async Task<DafnyDocument> HandleStatusUpdate(IImplementationTask implementationTask, VerificationStatus boogieStatus) {
        var id = GetImplementationId(implementationTask.Implementation);
        var status = await StatusFromImplementationTaskAsync(implementationTask);
        var lspRange = implementationTask.Implementation.tok.GetLspRange();
        if (boogieStatus is VerificationStatus.Completed) {
          var verificationResult = await implementationTask.ActualTask;
          foreach (var counterExample in verificationResult.Errors) {
            counterExamples.Push(counterExample);
          }

          var itDiagnostics = GetDiagnosticsFromResult(document, verificationResult);
          var view = new ImplementationView(lspRange, status, itDiagnostics);
          implementationViews.AddOrUpdate(id, view, (_, _) => view);
          if (VerifierOptions.GutterStatus) {
            progressReporter.ReportEndVerifyImplementation(implementationTask.Implementation, verificationResult);
          }
        } else {
          implementationViews.AddOrUpdate(id,
            _ => new ImplementationView(lspRange, status, Array.Empty<Diagnostic>()),
            (_, previousView) => previousView with { Status = status });
        }

        return document with {
          ImplementationViews = implementationViews.ToImmutableDictionary(),
          CounterExamples = counterExamples.ToArray(),
        };
      }
    }

    private void ReportRealtimeDiagnostics(DafnyDocument document, IObservable<DafnyDocument> result,
      IVerificationProgressReporter progressReporter, CancellationToken cancellationToken) {
      result.DefaultIfEmpty(document).LastAsync().Subscribe(finalDocument => {
        // All unvisited trees need to set them as "verified"
        if (!cancellationToken.IsCancellationRequested) {
          SetAllUnvisitedMethodsAsVerified(document);
        }

        progressReporter.ReportRealtimeDiagnostics(true, finalDocument);
      });
    }

    private static ConcurrentDictionary<ImplementationId, ImplementationView> GetExistingViews(DafnyDocument document, IReadOnlyList<IImplementationTask> implementationTasks) {
      var viewDictionary = new ConcurrentDictionary<ImplementationId, ImplementationView>();
      foreach (var task in implementationTasks) {
        var id = GetImplementationId(task.Implementation);
        if (document.ImplementationViews!.TryGetValue(id, out var existingView)) {
          viewDictionary.TryAdd(id, existingView);
        }
      }

      return viewDictionary;
    }

    private List<Diagnostic> GetDiagnosticsFromResult(DafnyDocument document, VerificationResult result) {
      var errorReporter = new DiagnosticErrorReporter(document.Uri);
      foreach (var counterExample in result.Errors) {
        errorReporter.ReportBoogieError(counterExample.CreateErrorInformation(result.Outcome, Options.ForceBplErrors));
      }

      var outcomeError = result.GetOutcomeError(Options);
      if (outcomeError != null) {
        errorReporter.ReportBoogieError(outcomeError);
      }

      return errorReporter.GetDiagnostics(document.Uri).OrderBy(d => d.Range.Start).ToList();
    }

    private async Task<PublishedVerificationStatus> StatusFromImplementationTaskAsync(IImplementationTask task) {
      switch (task.CurrentStatus) {
        case VerificationStatus.Stale: return PublishedVerificationStatus.Stale;
        case VerificationStatus.Queued:
          return PublishedVerificationStatus.Queued;
        case VerificationStatus.Running:
          return PublishedVerificationStatus.Running;
        case VerificationStatus.Completed:
          var verificationResult = await task.ActualTask;
          return verificationResult.Outcome == ConditionGeneration.Outcome.Correct
            ? PublishedVerificationStatus.Correct
            : PublishedVerificationStatus.Error;
        default:
          throw new ArgumentOutOfRangeException();
      }
    }

    protected virtual VerificationProgressReporter CreateVerificationProgressReporter(DafnyDocument document) {
      return new VerificationProgressReporter(
        loggerFactory.CreateLogger<VerificationProgressReporter>(),
        document, notificationPublisher, diagnosticPublisher);
    }

    private async Task NotifyStatusAsync(TextDocumentItem item, IObservable<DafnyDocument> documents, CancellationToken cancellationToken) {
      var finalDocument = await documents.ToTask(cancellationToken);
      var results = await Task.WhenAll(finalDocument.VerificationTasks!.Tasks.Select(t => t.ActualTask));
      logger.LogDebug($"Finished verification with {results.Sum(r => r.Errors.Count)} errors.");
      var verified = results.All(r => r.Outcome == ConditionGeneration.Outcome.Correct);
      var compilationStatusAfterVerification = verified
        ? CompilationStatus.VerificationSucceeded
        : CompilationStatus.VerificationFailed;
      notificationPublisher.SendStatusNotification(item, compilationStatusAfterVerification,
        cancellationToken.IsCancellationRequested ? "(cancelled)" : null);
    }

    // Called only in the case there is a parsing or resolution error on the document
    public void PublishGutterIcons(DafnyDocument document, bool verificationStarted) {
      diagnosticPublisher.PublishGutterIcons(document, verificationStarted);
    }

    private void SetAllUnvisitedMethodsAsVerified(DafnyDocument document) {
      foreach (var tree in document.VerificationTree.Children) {
        tree.SetVerifiedIfPending();
      }
    }

    static ImplementationId GetImplementationId(Implementation implementation) {
      var prefix = implementation.Name.Split(Translator.NameSeparator)[0];

      // Refining declarations get the token of what they're refining, so to distinguish them we need to
      // add the refining module name to the prefix.
      if (implementation.tok is RefinementToken refinementToken) {
        prefix += "." + refinementToken.InheritingModule.Name;
      }
      return new ImplementationId(implementation.tok.GetLspPosition(), prefix);
    }
  }
}


public record ImplementationId(Position NamedVerificationTask, string Name);
