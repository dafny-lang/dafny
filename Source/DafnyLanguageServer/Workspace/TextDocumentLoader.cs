using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class TextDocumentLoader : ITextDocumentLoader {
    private readonly IDafnyParser _parser;
    private readonly ISymbolResolver _symbolResolver;
    private readonly IProgramVerifier _verifier;
    private readonly ISymbolTableFactory _symbolTableFactory;
    private readonly IVerificationNotificationPublisher _notificationPublisher;

    public TextDocumentLoader(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      IVerificationNotificationPublisher notificationPublisher
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
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      var serializedCounterExamples = await VerifyIfEnabledAsync(textDocument, program, verify, cancellationToken);
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable, serializedCounterExamples);
    }

    private async Task<string?> VerifyIfEnabledAsync(TextDocumentItem textDocument, Dafny.Program program, bool verify, CancellationToken cancellationToken) {
      if(!verify) {
        return null;
      }
      _notificationPublisher.Started(textDocument);
      var verificationResult = await _verifier.VerifyAsync(program, cancellationToken);
      _notificationPublisher.Completed(textDocument, verificationResult.Verified);
      return verificationResult.SerializedCounterExamples;
    }
  }
}
