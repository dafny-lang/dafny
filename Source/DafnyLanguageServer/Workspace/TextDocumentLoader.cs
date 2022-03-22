using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;

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

    static readonly ThreadTaskScheduler LargeStackScheduler = new(MaxStackSize);

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
      return new DafnyDocument(textDocument, errorReporter, new List<Diagnostic>(), ghostDiagnostics, program, symbolTable);
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

    public Task<DafnyDocument> VerifyAsync(DafnyDocument document, CancellationToken cancellationToken) {

      return Task.Factory.StartNew(() => VerifyInternalAsync(document, cancellationToken), cancellationToken,
        TaskCreationOptions.None, LargeStackScheduler).Unwrap();
    }

    private async Task<DafnyDocument> VerifyInternalAsync(DafnyDocument document, CancellationToken cancellationToken) {
      notificationPublisher.SendStatusNotification(document.Text, CompilationStatus.VerificationStarted);
      var progressReporter = new VerificationProgressReporter(document.Text, notificationPublisher);
      var verificationResult = await verifier.VerifyAsync(document.Program, progressReporter, cancellationToken);
      var compilationStatusAfterVerification = verificationResult.Verified
        ? CompilationStatus.VerificationSucceeded
        : CompilationStatus.VerificationFailed;
      notificationPublisher.SendStatusNotification(document.Text, compilationStatusAfterVerification);
      logger.LogDebug($"Finished verification with {document.Errors.ErrorCount} errors.");
      return document with {
        OldVerificationDiagnostics = new List<Diagnostic>(),
        SerializedCounterExamples = verificationResult.SerializedCounterExamples
      };
    }

    private record Request(CancellationToken CancellationToken) {
      public TaskCompletionSource<DafnyDocument> Document { get; } = new();
    }

    private class VerificationProgressReporter : IVerificationProgressReporter {
      private ICompilationStatusNotificationPublisher publisher { get; init; }
      private TextDocumentItem document { get; init; }

      public VerificationProgressReporter(TextDocumentItem document,
                                          ICompilationStatusNotificationPublisher publisher) {
        this.document = document;
        this.publisher = publisher;
      }

      public void ReportProgress(string message) {
        publisher.SendStatusNotification(document, CompilationStatus.VerificationStarted, message);
      }
    }
  }
}
