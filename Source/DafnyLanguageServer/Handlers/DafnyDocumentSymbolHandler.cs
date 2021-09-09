using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  /// <summary>
  /// LSP Synchronization handler for symbol based events, i.e. the client requests the symbols of the specified document.
  /// </summary>
  public class DafnyDocumentSymbolHandler : DocumentSymbolHandlerBase {
    private static readonly SymbolInformationOrDocumentSymbol[] _emptySymbols = Array.Empty<SymbolInformationOrDocumentSymbol>();

    private readonly ILogger _logger;
    private readonly IDocumentDatabase _documents;

    public DafnyDocumentSymbolHandler(ILogger<DafnyDocumentSymbolHandler> logger, IDocumentDatabase documents) {
      _logger = logger;
      _documents = documents;
    }

    protected override DocumentSymbolRegistrationOptions CreateRegistrationOptions(DocumentSymbolCapability capability, ClientCapabilities clientCapabilities) {
      return new DocumentSymbolRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public override Task<SymbolInformationOrDocumentSymbolContainer> Handle(DocumentSymbolParams request, CancellationToken cancellationToken) {
      DafnyDocument? document;
      if (!_documents.TryGetDocument(request.TextDocument, out document)) {
        _logger.LogWarning("symbols requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return Task.FromResult<SymbolInformationOrDocumentSymbolContainer>(_emptySymbols);
      }
      var visitor = new LspSymbolGeneratingVisitor(document.SymbolTable, cancellationToken);
      var symbols = visitor.Visit(document.SymbolTable.CompilationUnit)
        .Select(symbol => new SymbolInformationOrDocumentSymbol(symbol))
        .ToArray();
      return Task.FromResult<SymbolInformationOrDocumentSymbolContainer>(symbols);
    }
  }
}
