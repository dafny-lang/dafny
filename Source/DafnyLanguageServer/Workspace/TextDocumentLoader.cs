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
using System.Reactive.Threading.Tasks;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using VC;

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
    protected readonly INotificationPublisher NotificationPublisher;

    protected TextDocumentLoader(
      ILoggerFactory loggerFactory,
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher statusPublisher,
      INotificationPublisher notificationPublisher,
      VerifierOptions verifierOptions) {
      VerifierOptions = verifierOptions;
      this.parser = parser;
      this.symbolResolver = symbolResolver;
      this.verifier = verifier;
      this.symbolTableFactory = symbolTableFactory;
      this.ghostStateDiagnosticCollector = ghostStateDiagnosticCollector;
      this.notificationPublisher = statusPublisher;
      this.loggerFactory = loggerFactory;
      logger = loggerFactory.CreateLogger<TextDocumentLoader>();
      NotificationPublisher = notificationPublisher;
    }

    public static TextDocumentLoader Create(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher statusPublisher,
      ILoggerFactory loggerFactory,
      INotificationPublisher notificationPublisher,
      VerifierOptions verifierOptions
      ) {
      return new TextDocumentLoader(loggerFactory, parser, symbolResolver, verifier, symbolTableFactory, ghostStateDiagnosticCollector, statusPublisher, notificationPublisher, verifierOptions);
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
      if (loaded.ParseAndResolutionDiagnostics.Any(d =>
            d.Severity == DiagnosticSeverity.Error &&
            d.Source != MessageSource.Compiler.ToString() &&
            d.Source != MessageSource.Verifier.ToString())) {
        throw new TaskCanceledException();
      }

      var verificationTasks = await verifier.GetVerificationTasksAsync(loaded, cancellationToken);
      var initialViews = new ConcurrentDictionary<ImplementationId, ImplementationView>();

      foreach (var task in verificationTasks) {
        var status = StatusFromBoogieStatus(task.CacheStatus);
        var id = GetImplementationId(task.Implementation);
        if (task.CacheStatus is Completed completed) {
          var view = new ImplementationView(task.Implementation.tok.GetLspRange(), status, GetDiagnosticsFromResult(loaded, completed.Result));
          initialViews.TryAdd(GetImplementationId(task.Implementation), view);
        } else if (loaded.ImplementationViewsView!.TryGetValue(id, out var existingView)) {
          initialViews.TryAdd(id, existingView with { Status = status });
        } else {
          var view = new ImplementationView(task.Implementation.tok.GetLspRange(), status, Array.Empty<Diagnostic>());
          initialViews.TryAdd(GetImplementationId(task.Implementation), view);
        }
      }

      var result = loaded with {
        Counterexamples = new ConcurrentStack<Counterexample>(),
        ImplementationViews = initialViews,
        VerificationTasks = verificationTasks,
        ImplementationViewsView = initialViews.ToImmutableDictionary(),
      };
      var progressReporter = CreateVerificationProgressReporter(result);
      if (VerifierOptions.GutterStatus) {
        progressReporter.RecomputeVerificationTree();
        progressReporter.ReportRealtimeDiagnostics(false, result);
        progressReporter.ReportImplementationsBeforeVerification(
          verificationTasks.Select(t => t.Implementation).ToArray());
      }
      var implementations = verificationTasks.Select(t => t.Implementation).ToHashSet();
      var subscription = verifier.BatchCompletions.Where(c =>
        implementations.Contains(c.Split.Implementation)).Subscribe(progressReporter.ReportAssertionBatchResult);
      cancellationToken.Register(() => subscription.Dispose());
      result.GutterProgressReporter = progressReporter;
      return result;
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

      var compilationUnit = symbolResolver.ResolveSymbols(textDocument, program, out var canDoVerification, cancellationToken);
      var symbolTable = symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      if (errorReporter.HasErrors) {
        notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.ResolutionFailed);
      } else {
        notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.CompilationSucceeded);
      }
      var ghostDiagnostics = ghostStateDiagnosticCollector.GetGhostStateDiagnostics(symbolTable, cancellationToken).ToArray();

      return new DafnyDocument(textDocument,
        errorReporter.GetDiagnostics(textDocument.Uri),
        canDoVerification,
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
      var parseAndResolutionDiagnostics = errorReporter.GetDiagnostics(textDocument.Uri);
      return new DafnyDocument(
        textDocument,
        errorReporter.GetDiagnostics(textDocument.Uri),
        false,
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

    public IObservable<DafnyDocument> VerifyAllTasks(DafnyDocument document, CancellationToken cancellationToken) {
      notificationPublisher.SendStatusNotification(document.TextDocumentItem, CompilationStatus.VerificationStarted);

      var implementationTasks = document.VerificationTasks!;

      var result = implementationTasks.Select(task => Verify(document, task, cancellationToken)).Merge().
        Where(d => implementationTasks.All(t => {
          var taskStatus = d.ImplementationViewsView![GetImplementationId(t.Implementation)].Status;
          return taskStatus != PublishedVerificationStatus.Stale;
        })).Replay();
      result.Connect();

      if (VerifierOptions.GutterStatus) {
        ReportRealtimeDiagnostics(document, result, cancellationToken);
      }

      var _ = NotifyStatusAsync(document.TextDocumentItem, result.DefaultIfEmpty(document), cancellationToken);
      return result;
    }

    public IObservable<DafnyDocument> Verify(DafnyDocument dafnyDocument, IImplementationTask implementationTask, CancellationToken cancellationToken) {

      if (VerifierOptions.GutterStatus) {
        dafnyDocument.GutterProgressReporter!.ReportStartVerifyImplementation(implementationTask.Implementation);
      }

      try {
        var observable = implementationTask.Run();
        cancellationToken.Register(() => {
          try {
            implementationTask.Cancel();
          } catch (InvalidOperationException e) {
            if (!e.Message.Contains("no ongoing run")) {
              throw;
            }
          }
        });
        return GetVerifiedDafnyDocuments(dafnyDocument, implementationTask, observable);
      } catch (InvalidOperationException e) {
        if (e.Message.Contains("already completed") || e.Message.Contains("ongoing run")) {
          return Observable.Empty<DafnyDocument>();
        }

        throw;
      }
    }

    private IObservable<DafnyDocument> GetVerifiedDafnyDocuments(DafnyDocument document, IImplementationTask implementationTask,
      IObservable<IVerificationStatus> statusUpdates) {

      var result = statusUpdates.Select(boogieStatus => HandleStatusUpdate(document, implementationTask, boogieStatus));

      var initial = document with {
        ImplementationViewsView = document.ImplementationViews!.ToImmutableDictionary(),
      };
      return Observable.Return(initial).Concat(result);
    }

    DafnyDocument HandleStatusUpdate(DafnyDocument document, IImplementationTask implementationTask, IVerificationStatus boogieStatus) {
      var id = GetImplementationId(implementationTask.Implementation);
      var status = StatusFromBoogieStatus(boogieStatus);
      var implementationRange = implementationTask.Implementation.tok.GetLspRange();
      if (boogieStatus is Completed completed) {
        var verificationResult = completed.Result;
        foreach (var counterExample in verificationResult.Errors) {
          document.Counterexamples!.Push(counterExample);
        }

        var itDiagnostics = GetDiagnosticsFromResult(document, verificationResult);
        var view = new ImplementationView(lspRange, status, itDiagnostics);
        document.ImplementationViews!.AddOrUpdate(id, view, (_, _) => view);
        if (VerifierOptions.GutterStatus) {
          document.GutterProgressReporter!.ReportEndVerifyImplementation(implementationTask.Implementation, verificationResult);
        }
      } else {
        document.ImplementationViews!.AddOrUpdate(id,
          _ => new ImplementationView(lspRange, status, Array.Empty<Diagnostic>()),
          (_, previousView) => previousView with { Status = status });
      }

      return document with {
        ImplementationViewsView = document.ImplementationViews.ToImmutableDictionary(),
        CounterExamplesView = document.Counterexamples!.ToArray(),
      };
    }

    private void ReportRealtimeDiagnostics(DafnyDocument document, IObservable<DafnyDocument> result, CancellationToken cancellationToken) {
      result.DefaultIfEmpty(document).LastAsync().Subscribe(finalDocument => {
        // All unvisited trees need to set them as "verified"
        if (!cancellationToken.IsCancellationRequested) {
          SetAllUnvisitedMethodsAsVerified(document);
        }

        document.GutterProgressReporter!.ReportRealtimeDiagnostics(true, finalDocument);
      });
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

    private PublishedVerificationStatus StatusFromBoogieStatus(IVerificationStatus verificationStatus) {
      switch (verificationStatus) {
        case Stale:
          return PublishedVerificationStatus.Stale;
        case Queued:
          return PublishedVerificationStatus.Queued;
        case Running:
          return PublishedVerificationStatus.Running;
        case Completed completed:
          return completed.Result.Outcome == ConditionGeneration.Outcome.Correct
            ? PublishedVerificationStatus.Correct
            : PublishedVerificationStatus.Error;
        default:
          throw new ArgumentOutOfRangeException();
      }
    }

    protected virtual VerificationProgressReporter CreateVerificationProgressReporter(DafnyDocument document) {
      return new VerificationProgressReporter(
        loggerFactory.CreateLogger<VerificationProgressReporter>(),
        document, notificationPublisher, NotificationPublisher);
    }

    private async Task NotifyStatusAsync(TextDocumentItem item, IObservable<DafnyDocument> documents, CancellationToken cancellationToken) {
      var finalDocument = await documents.ToTask(cancellationToken);
      var errorCount = finalDocument.ImplementationViewsView!.Values.Sum(r => r.Diagnostics.Count(d => d.Severity == DiagnosticSeverity.Error));
      logger.LogDebug($"Finished verification with {errorCount} errors.");
      var verified = errorCount == 0;
      var compilationStatusAfterVerification = verified
        ? CompilationStatus.VerificationSucceeded
        : CompilationStatus.VerificationFailed;
      notificationPublisher.SendStatusNotification(item, compilationStatusAfterVerification,
        cancellationToken.IsCancellationRequested ? "(cancelled)" : null);
    }

    // Called only in the case there is a parsing or resolution error on the document
    public void PublishGutterIcons(DafnyDocument document, bool verificationStarted) {
      NotificationPublisher.PublishGutterIcons(document, verificationStarted);
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
