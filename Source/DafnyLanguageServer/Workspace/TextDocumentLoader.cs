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
using Microsoft.Extensions.Options;
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
    public VerifierOptions VerifierOptions { get; }
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

      return new DafnyDocument(Options, textDocument, errorReporter.GetDiagnostics(textDocument.Uri),
        new Dictionary<ImplementationId, IReadOnlyList<Diagnostic>>(),
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
        Options,
        textDocument,
        errorReporter.GetDiagnostics(textDocument.Uri),
        new Dictionary<ImplementationId, IReadOnlyList<Diagnostic>>(),
        Array.Empty<Counterexample>(),
        Array.Empty<Diagnostic>(),
        program,
        CreateEmptySymbolTable(program, logger),
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
      var programErrorReporter = new DiagnosticErrorReporter(document.Uri);
      document.Program.Reporter = programErrorReporter;
      var implementationTasks = verifier.Verify(document, progressReporter);
      foreach (var task in implementationTasks) {
        cancellationToken.Register(task.Cancel);
      }
      foreach (var implementationTask in implementationTasks) {
        implementationTask.Run();
      }

      var _ = NotifyStatusAsync(document.TextDocumentItem, implementationTasks, cancellationToken);

      var concurrentDictionary = new ConcurrentDictionary<ImplementationId, IReadOnlyList<Diagnostic>>();
      foreach (var task in implementationTasks) {
        var id = GetImplementationId(task.Implementation);
        if (document.VerificationDiagnosticsPerImplementation.TryGetValue(id, out var existingDiagnostics)) {
          concurrentDictionary.TryAdd(id, existingDiagnostics);
        }
      }
      var counterExamples = new ConcurrentStack<Counterexample>();
      var documentTasks = implementationTasks.Select(async implementationTask => {
        var result = await implementationTask.ActualTask;
        var id = GetImplementationId(implementationTask.Implementation);

        var errorReporter = new DiagnosticErrorReporter(document.Uri);
        foreach (var counterExample in result.Errors) {
          counterExamples.Push(counterExample);
          errorReporter.ReportBoogieError(counterExample.CreateErrorInformation(result.Outcome, Options.ForceBplErrors));
        }
        var outcomeError = result.GetOutcomeError(Options);
        if (outcomeError != null) {
          errorReporter.ReportBoogieError(outcomeError);
        }

        var diagnostics = errorReporter.GetDiagnostics(document.Uri).OrderBy(d => d.Range.Start).ToList();
        concurrentDictionary.AddOrUpdate(id, diagnostics, (_, _) => diagnostics);

        return document with {
          VerificationDiagnosticsPerImplementation = concurrentDictionary.ToImmutableDictionary(),
          CounterExamples = counterExamples.ToArray(),
        };
      }).ToList();
      var result = documentTasks.Select(documentTask => documentTask.ToObservable()).Merge();
      result.DefaultIfEmpty(document).LastAsync().Subscribe(finalDocument => {

        // All unvisited trees need to set them as "verified"
        if (!cancellationToken.IsCancellationRequested) {
          SetAllUnvisitedMethodsAsVerified(document);
        }

        if (VerifierOptions.GutterStatus) {
          progressReporter.ReportRealtimeDiagnostics(true, finalDocument);
        }
      });
      return result;
    }

    protected virtual VerificationProgressReporter CreateVerificationProgressReporter(DafnyDocument document) {
      return new VerificationProgressReporter(
        loggerFactory.CreateLogger<VerificationProgressReporter>(),
        document, notificationPublisher, diagnosticPublisher);
    }

    private async Task NotifyStatusAsync(TextDocumentItem item, IReadOnlyList<IImplementationTask> implementationTasks, CancellationToken cancellationToken) {
      var results = await Task.WhenAll(implementationTasks.Select(t => t.ActualTask));
      logger.LogDebug($"Finished verification with {results.Sum(r => r.Errors.Count)} errors.");
      var verified = results.All(r => r.Outcome == ConditionGeneration.Outcome.Correct);
      var compilationStatusAfterVerification = verified
        ? CompilationStatus.VerificationSucceeded
        : CompilationStatus.VerificationFailed;
      notificationPublisher.SendStatusNotification(item, compilationStatusAfterVerification,
        cancellationToken.IsCancellationRequested ? "(cancelled)" : null);
    }

    // Called only in the case there is a parsing or resolution error on the document
    public void PublishVerificationDiagnostics(DafnyDocument document, bool verificationStarted) {
      diagnosticPublisher.PublishVerificationDiagnostics(document, verificationStarted);
    }

    private void SetAllUnvisitedMethodsAsVerified(DafnyDocument document) {
      foreach (var tree in document.VerificationTree.Children) {
        tree.SetVerifiedIfPending();
      }
    }

    static ImplementationId GetImplementationId(Implementation implementation) {
      var prefix = implementation.Name.Split(Translator.NameSeparator)[0];
      return new ImplementationId(implementation.tok.GetLspPosition(), prefix);
    }
  }
}


public record ImplementationId(Position NamedVerificationTask, string Name);
