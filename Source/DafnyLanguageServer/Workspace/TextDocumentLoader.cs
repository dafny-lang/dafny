using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Text document loader implementation that offloads the whole procedure on one dedicated
  /// thread with a stack size of 256MB.
  /// </summary>
  /// <remarks>
  /// The increased stack size is necessary to solve the issue https://github.com/dafny-lang/dafny/issues/1447.
  /// </remarks>
  public class TextDocumentLoader : ITextDocumentLoader {
    // 256MB
    private const int MaxStackSize = 0x10000000;

    private readonly IDafnyParser parser;
    private readonly ISymbolResolver symbolResolver;
    private readonly IProgramVerifier verifier;
    private readonly ISymbolTableFactory symbolTableFactory;
    private readonly ICompilationStatusNotificationPublisher notificationPublisher;

    private readonly Thread loadThread;
    private readonly BlockingCollection<LoadRequest> loadRequests = new();

    private TextDocumentLoader(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      ICompilationStatusNotificationPublisher notificationPublisher
    ) {
      this.parser = parser;
      this.symbolResolver = symbolResolver;
      this.verifier = verifier;
      this.symbolTableFactory = symbolTableFactory;
      this.notificationPublisher = notificationPublisher;
      loadThread = new(LoadLoop, MaxStackSize) { IsBackground = true };
    }

    public static TextDocumentLoader Create(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      ICompilationStatusNotificationPublisher notificationPublisher
    ) {
      var loader = new TextDocumentLoader(parser, symbolResolver, verifier, symbolTableFactory, notificationPublisher);
      loader.loadThread.Start();
      return loader;
    }

    public async Task<DafnyDocument> LoadAsync(TextDocumentItem textDocument, bool verify, CancellationToken cancellationToken) {
      var request = new LoadRequest(textDocument, verify, cancellationToken);
      loadRequests.Add(request, cancellationToken);
      return await request.Document.Task;
    }

    private void LoadLoop() {
      for(; ;) {
        var request = loadRequests.Take();
        var document = LoadInternal(request);
        request.Document.SetResult(document);
      }
    }

    private DafnyDocument LoadInternal(LoadRequest loadRequest) {
      var (textDocument, verify, cancellationToken) = loadRequest;
      var errorReporter = new DiagnosticErrorReporter(textDocument.Uri);
      var program = parser.Parse(textDocument, errorReporter, cancellationToken);
      if (errorReporter.HasErrors) {
        notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.ParsingFailed);
        return CreateDocumentWithParserErrors(textDocument, errorReporter, program);
      }
      var compilationUnit = symbolResolver.ResolveSymbols(textDocument, program, cancellationToken);
      var symbolTable = symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      string? serializedCounterExamples;
      if (errorReporter.HasErrors) {
        notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.ResolutionFailed);
        serializedCounterExamples = null;
      } else {
        notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.CompilationSucceeded);
        serializedCounterExamples = VerifyIfEnabled(textDocument, program, verify, cancellationToken);
      }
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }

    private static DafnyDocument CreateDocumentWithParserErrors(TextDocumentItem textDocument, DiagnosticErrorReporter errorReporter, Dafny.Program program) {
      return new DafnyDocument(
        textDocument,
        errorReporter,
        program,
        CreateEmptySymbolTable(program),
        serializedCounterExamples: null
      );
    }

    private static SymbolTable CreateEmptySymbolTable(Dafny.Program program) {
      return new SymbolTable(
        new CompilationUnit(program),
        new Dictionary<object, ILocalizableSymbol>(),
        new Dictionary<ISymbol, SymbolLocation>(),
        new IntervalTree<Position, ILocalizableSymbol>(),
        symbolsResolved: false
      );
    }

    private string? VerifyIfEnabled(TextDocumentItem textDocument, Dafny.Program program, bool verify, CancellationToken cancellationToken) {
      if (!verify) {
        return null;
      }
      notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.VerificationStarted);
      var verificationResult = verifier.Verify(program, cancellationToken);
      var compilationStatusAfterVerification = verificationResult.Verified
        ? CompilationStatus.VerificationSucceeded
        : CompilationStatus.VerificationFailed;
      notificationPublisher.SendStatusNotification(textDocument, compilationStatusAfterVerification);
      return verificationResult.SerializedCounterExamples;
    }

    private record LoadRequest(TextDocumentItem TextDocument, bool Verify, CancellationToken CancellationToken) {
      public TaskCompletionSource<DafnyDocument> Document { get; } = new();
    }
  }
}
