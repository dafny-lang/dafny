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
using System.Text.RegularExpressions;
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
    private const int ResolverMaxStackSize = 0x10000000; // 256MB
    private static readonly ThreadTaskScheduler ResolverScheduler = new(ResolverMaxStackSize);

    private DafnyOptions Options => DafnyOptions.O;
    private readonly IDafnyParser parser;
    private readonly ISymbolResolver symbolResolver;
    private readonly ISymbolTableFactory symbolTableFactory;
    private readonly IProgramVerifier verifier;
    private readonly IGhostStateDiagnosticCollector ghostStateDiagnosticCollector;
    private readonly ICompilationStatusNotificationPublisher notificationPublisher;
    private readonly ILoggerFactory loggerFactory;
    private readonly ILogger<TextDocumentLoader> logger;

    private TextDocumentLoader(
      ILoggerFactory loggerFactory,
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher notificationPublisher) {
      this.parser = parser;
      this.symbolResolver = symbolResolver;
      this.verifier = verifier;
      this.symbolTableFactory = symbolTableFactory;
      this.ghostStateDiagnosticCollector = ghostStateDiagnosticCollector;
      this.notificationPublisher = notificationPublisher;
      this.loggerFactory = loggerFactory;
      this.logger = loggerFactory.CreateLogger<TextDocumentLoader>();
    }

    public static TextDocumentLoader Create(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher notificationPublisher,
      ILoggerFactory loggerFactory
      ) {
      return new TextDocumentLoader(loggerFactory, parser, symbolResolver, verifier, symbolTableFactory, ghostStateDiagnosticCollector, notificationPublisher);
    }

    public DafnyDocument CreateUnloaded(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      var errorReporter = new DiagnosticErrorReporter(textDocument.Uri);
      return CreateDocumentWithEmptySymbolTable(
        loggerFactory.CreateLogger<SymbolTable>(),
        textDocument,
        errorReporter,
        parser.CreateUnparsed(textDocument, errorReporter, cancellationToken),
        loadCanceled: true
      );
    }

    public async Task<DafnyDocument> LoadAndPrepareVerificationTasksAsync(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      var loaded = await LoadAsync(textDocument, cancellationToken);
      if (loaded.ParseAndResolutionDiagnostics.Any(d => d.Severity == DiagnosticSeverity.Error)) {
        return loaded;
      }
      return loaded with {
        VerificationTasks = verifier.Verify(loaded.Program, cancellationToken),
      };
    }

    public async Task<DafnyDocument> LoadAsync(TextDocumentItem textDocument, CancellationToken cancellationToken) {
#pragma warning disable CS1998
      return await await Task.Factory.StartNew(async () => LoadInternal(textDocument, cancellationToken), cancellationToken,
#pragma warning restore CS1998
        TaskCreationOptions.None, ResolverScheduler);
    }

    private DafnyDocument LoadInternal(TextDocumentItem textDocument, CancellationToken cancellationToken) {
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
        Array.Empty<IImplementationTask>(),
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
      TextDocumentItem textDocument,
      DiagnosticErrorReporter errorReporter,
      Dafny.Program program,
      bool loadCanceled
    ) {
      return new DafnyDocument(
        textDocument,
        errorReporter.GetDiagnostics(textDocument.Uri),
        Array.Empty<IImplementationTask>(),
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

      var implementationTasks = document.VerificationTasks;
      var _ = NotifyStatusAsync(document.TextDocumentItem, implementationTasks);

      var concurrentDictionary = new ConcurrentDictionary<ImplementationId, IReadOnlyList<Diagnostic>>();
      foreach (var task in implementationTasks) {
        var id = GetImplementationId(task.Implementation);
        if (document.VerificationDiagnosticsPerImplementation.TryGetValue(id, out var existingDiagnostics)) {
          concurrentDictionary.TryAdd(id, existingDiagnostics);
        }
      }
      var counterExamples = new ConcurrentStack<Counterexample>();

      // TODO consider moving this inside the `result definition
      var diagnostics = implementationTasks.ToDictionary(it => it, async implementationTask => {
        var result = await implementationTask.ActualTask;

        cancellationToken.ThrowIfCancellationRequested();

        var errorReporter = new DiagnosticErrorReporter(document.Uri);
        foreach (var counterExample in result.Errors) {
          counterExamples.Push(counterExample);
          errorReporter.ReportBoogieError(counterExample.CreateErrorInformation(result.Outcome, Options.ForceBplErrors));
        }
        var outcomeError = result.GetOutcomeError(Options);
        if (outcomeError != null) {
          errorReporter.ReportBoogieError(outcomeError);
        }

        return errorReporter.GetDiagnostics(document.Uri).OrderBy(d => d.Range.Start).ToList();
      });

      var result = implementationTasks.Select(implementationTask => implementationTask.ObservableStatus.Select(async _ => {
        if (implementationTask.CurrentStatus is VerificationStatus.Completed) {
          var itDiagnostics = await diagnostics[implementationTask];
          var id = GetImplementationId(implementationTask.Implementation);


          concurrentDictionary.AddOrUpdate(id, itDiagnostics, (_, _) => itDiagnostics);
        }

        if (implementationTask.CurrentStatus is VerificationStatus.Running) {
          // For backwards compatibility

          var match = Regex.Match(implementationTask.Implementation.Name, "^.+[.](?<name>[^.]+)$");
          if (match.Success) {
            notificationPublisher.SendStatusNotification(document.TextDocumentItem, CompilationStatus.VerificationStarted, match.Groups["name"].Value);
          }
        }

        return document with {
          VerificationTasks = implementationTasks,
          VerificationDiagnosticsPerImplementation = concurrentDictionary.ToImmutableDictionary(),
          CounterExamples = counterExamples.ToArray(),
        };
      }).SelectMany(t => t.ToObservable())).Merge().Replay();
      result.Connect();

      foreach (var implementationTask in document.VerificationTasks) {
        implementationTask.Run();
      }

      return result;
    }

    private async Task NotifyStatusAsync(TextDocumentItem item, IReadOnlyList<IImplementationTask> implementationTasks) {
      var results = await Task.WhenAll(implementationTasks.Select(t => t.ActualTask));
      logger.LogDebug($"Finished verification with {results.Sum(r => r.Errors.Count)} errors.");
      var verified = results.All(r => r.Outcome == ConditionGeneration.Outcome.Correct);
      var compilationStatusAfterVerification = verified
        ? CompilationStatus.VerificationSucceeded
        : CompilationStatus.VerificationFailed;
      notificationPublisher.SendStatusNotification(item, compilationStatusAfterVerification);
    }

    ImplementationId GetImplementationId(Implementation implementation) {
      var prefix = implementation.Name.Split(Translator.NameSeparator)[0];
      return new ImplementationId(implementation.tok.GetLspPosition(), prefix);
    }
  }
}


public record ImplementationId(Position NamedVerificationTask, string Name);
