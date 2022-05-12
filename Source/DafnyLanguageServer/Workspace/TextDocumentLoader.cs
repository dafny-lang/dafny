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
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
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
    // 256MB
    private const int MaxStackSize = 0x10000000;

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
      IDiagnosticPublisher diagnosticPublisher) {
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

    static readonly ThreadTaskScheduler LargeStackScheduler = new(MaxStackSize);

    public static TextDocumentLoader Create(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher notificationPublisher,
      ILoggerFactory loggerFactory,
      IDiagnosticPublisher diagnosticPublisher
      ) {
      return new TextDocumentLoader(loggerFactory, parser, symbolResolver, verifier, symbolTableFactory, ghostStateDiagnosticCollector, notificationPublisher, diagnosticPublisher);
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

    public Task<DafnyDocument> LoadAsync(TextDocumentItem textDocument, CancellationToken cancellationToken) {
#pragma warning disable CS1998
      // By using `async`, any OperationCancelledExceptions are converted to a cancelled Task.
      return Task.Factory.StartNew(async () => LoadInternal(textDocument, cancellationToken), cancellationToken,
        TaskCreationOptions.None, LargeStackScheduler).Unwrap();
#pragma warning restore CS1998
    }

    private DafnyDocument LoadInternal(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      var errorReporter = new DiagnosticErrorReporter(textDocument.Uri);
      var program = parser.Parse(textDocument, errorReporter, cancellationToken);
      PublishDafnyLanguageServerLoadErrors(errorReporter, program);
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
      return new DafnyDocument(textDocument, errorReporter, new List<Diagnostic>(), ghostDiagnostics, program, symbolTable) {
        ResolutionSucceeded = !errorReporter.HasErrors
      };
    }

    private static void PublishDafnyLanguageServerLoadErrors(DiagnosticErrorReporter errorReporter, Dafny.Program program) {
      foreach (var error in DafnyLanguageServer.LoadErrors) {
        errorReporter.Error(MessageSource.Compiler, program.GetFirstTopLevelToken(), error);
      }
    }

    private static DafnyDocument CreateDocumentWithEmptySymbolTable(
      ILogger<SymbolTable> logger,
      TextDocumentItem textDocument,
      DiagnosticErrorReporter errorReporter,
      Dafny.Program program,
      bool loadCanceled
    ) {
      return new DafnyDocument(
        textDocument,
        errorReporter,
        new List<Diagnostic>(),
        Array.Empty<Diagnostic>(),
        program,
        CreateEmptySymbolTable(program, logger),
        loadCanceled
      ) {
        ResolutionSucceeded = loadCanceled ? null : false
      };
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

    public Task<DafnyDocument> VerifyAsync(DafnyDocument document, CancellationToken cancellationToken) {

      return Task.Factory.StartNew(() => VerifyInternalAsync(document, cancellationToken), cancellationToken,
        TaskCreationOptions.None, LargeStackScheduler).Unwrap();
    }

    // Called only in the case there is a parsing or resolution error on the document
    public void PublishVerificationDiagnostics(DafnyDocument document, bool verificationStarted) {
      diagnosticPublisher.PublishVerificationDiagnostics(document, verificationStarted);
    }

    public virtual VerificationProgressReporter CreateVerificationProgressReporter(DafnyDocument document) {
      return new VerificationProgressReporter(
        loggerFactory.CreateLogger<VerificationProgressReporter>(),
        document, notificationPublisher, diagnosticPublisher);
    }

    private async Task<DafnyDocument> VerifyInternalAsync(DafnyDocument document, CancellationToken cancellationToken) {
      notificationPublisher.SendStatusNotification(document.Text, CompilationStatus.VerificationStarted);
      var progressReporter = CreateVerificationProgressReporter(document);
      var verificationResult = await verifier.VerifyAsync(document, progressReporter, cancellationToken);
      var compilationStatusAfterVerification = verificationResult.Verified
        ? CompilationStatus.VerificationSucceeded
        : CompilationStatus.VerificationFailed;
      // All unvisited trees need to set them as "verified"
      if (!cancellationToken.IsCancellationRequested) {
        SetAllUnvisitedMethodsAsVerified(document);
      }

      notificationPublisher.SendStatusNotification(document.Text, compilationStatusAfterVerification, cancellationToken.IsCancellationRequested ? "(cancelled)" : null);
      logger.LogDebug($"Finished verification with {document.Errors.ErrorCount} errors.");
      var newDocument = document with {
        OldVerificationDiagnostics = new List<Diagnostic>(),
        SerializedCounterExamples = verificationResult.SerializedCounterExamples,
      };
      progressReporter.ReportRealtimeDiagnostics(true, newDocument);
      return newDocument;
    }

    private void SetAllUnvisitedMethodsAsVerified(DafnyDocument document) {
      foreach (var tree in document.VerificationTree.Children) {
        tree.SetVerifiedIfPending();
      }
    }

    private record Request(CancellationToken CancellationToken) {
      public TaskCompletionSource<DafnyDocument> Document { get; } = new();
    }
  }
}
