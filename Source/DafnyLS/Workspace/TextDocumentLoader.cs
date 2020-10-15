using DafnyLS.Language;
using DafnyLS.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Workspace {
  internal class TextDocumentLoader : ITextDocumentLoader {
    private readonly IDafnyParser _parser;
    private readonly ISymbolResolver _symbolResolver;
    private readonly IProgramVerifier _verifier;
    private readonly ISymbolTableFactory _symbolTableFactory;

    public TextDocumentLoader(IDafnyParser parser, ISymbolResolver symbolResolver, IProgramVerifier verifier, ISymbolTableFactory symbolTableFactory) {
      _parser = parser;
      _symbolResolver = symbolResolver;
      _verifier = verifier;
      _symbolTableFactory = symbolTableFactory;
    }

    public async Task<DafnyDocument> LoadAsync(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var compilationUnit = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      var symbolTable = _symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      //var symbolLookup = SymbolLookup.FromSymbolTable(symbolTable, cancellationToken);
      await _verifier.VerifyAsync(program, cancellationToken);
      return new DafnyDocument(textDocument, errorReporter, program, compilationUnit, symbolTable);
    }
  }
}
