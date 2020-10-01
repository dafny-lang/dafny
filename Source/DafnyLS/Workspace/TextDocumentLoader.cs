using DafnyLS.Language;
using DafnyLS.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Workspace {
  internal class TextDocumentLoader : ITextDocumentLoader {
    private readonly IDafnyParser _parser;
    private readonly ISymbolResolver _symbolResolver;

    public TextDocumentLoader(IDafnyParser parser, ISymbolResolver symbolResolver) {
      _parser = parser;
      _symbolResolver = symbolResolver;
    }

    public async Task<DafnyDocument> LoadAsync(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      var symbolTable = await _symbolResolver.ResolveSymbolsAsync(textDocument, program, cancellationToken);
      return new DafnyDocument(textDocument, errorReporter, program, symbolTable);
    }
  }
}
