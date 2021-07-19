using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class TextDocumentLoader : ITextDocumentLoader {
    private readonly IDafnyParser _parser;
    private readonly ISymbolResolver _symbolResolver;
    private readonly IProgramVerifier _verifier;
    private readonly ISymbolTableFactory _symbolTableFactory;
    private readonly ICompilationStatusNotificationPublisher _notificationPublisher;

    public TextDocumentLoader(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      ICompilationStatusNotificationPublisher notificationPublisher
    ) {
      _parser = parser;
      _symbolResolver = symbolResolver;
      _verifier = verifier;
      _symbolTableFactory = symbolTableFactory;
      _notificationPublisher = notificationPublisher;
    }

    public async Task<DafnyDocument> LoadAsync(TextDocumentItem textDocument, bool verify, CancellationToken cancellationToken) {
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      if(errorReporter.HasErrors) {
        _notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.ParsingFailed);
        return CreateDocumentWithParserErrors(textDocument, errorReporter, program);
      }
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      string? serializedCounterExamples;
      if(errorReporter.HasErrors) {
        _notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.ResolutionFailed);
        serializedCounterExamples = null;
      } else {
        _notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.CompilationSucceeded);
        serializedCounterExamples = await VerifyIfEnabledAsync(textDocument, program, verify, cancellationToken);
      }
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }

    private static DafnyDocument CreateDocumentWithParserErrors(TextDocumentItem textDocument, ErrorReporter errorReporter, Dafny.Program program) {
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

    private async Task<string?> VerifyIfEnabledAsync(TextDocumentItem textDocument, Dafny.Program program, bool verify, CancellationToken cancellationToken) {
      if(!verify) {
        return null;
      }
      _notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.VerificationStarted);
      var verificationResult = await _verifier.VerifyAsync(program, cancellationToken);
      var compilationStatusAfterVerification = verificationResult.Verified
        ? CompilationStatus.VerificationSucceeded
        : CompilationStatus.VerificationFailed;
      _notificationPublisher.SendStatusNotification(textDocument, compilationStatusAfterVerification);
      return verificationResult.SerializedCounterExamples;
    }
  }
}
