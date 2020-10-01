using DafnyLS.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Handlers {
  /// <summary>
  /// LSP Synchronization handler for symbol based events, i.e. the client requests the symbols of the specified document.
  /// </summary>
  internal class DafnyDocumentSymbolHandler : DocumentSymbolHandler {
    private static readonly SymbolInformationOrDocumentSymbol[] _emptySymbols = new SymbolInformationOrDocumentSymbol[0];

    private readonly ILogger _logger;
    private readonly IDocumentDatabase _documents;
    private readonly ISymbolResolver _symbolResolver;

    public DafnyDocumentSymbolHandler(ILogger<DafnyDocumentSymbolHandler> logger, IDocumentDatabase documents, ISymbolResolver symbolResolver) : base(CreateRegistrationOptions()) {
      _logger = logger;
      _documents = documents;
      _symbolResolver = symbolResolver;
    }

    private static DocumentSymbolRegistrationOptions CreateRegistrationOptions() {
      return new DocumentSymbolRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public async override Task<SymbolInformationOrDocumentSymbolContainer> Handle(DocumentSymbolParams request, CancellationToken cancellationToken) {
      TextDocumentItem? document;
      if (!_documents.TryGetDocument(request.TextDocument, out document)) {
        _logger.LogWarning("symbols requested for unloaded document {}", request.TextDocument.Uri);
        return _emptySymbols;
      }
      var symbols = (await _symbolResolver.GetSymbolsAsync(document, cancellationToken)).ToArray();
      _logger.LogDebug("resolved {} symbols for {}", symbols.Length, document.Uri);
      return symbols;
    }
  }
}
