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
  public class DafnyFoldingRangeHandler : FoldingRangeHandlerBase {
    private static readonly SymbolInformationOrDocumentSymbol[] EmptySymbols = Array.Empty<SymbolInformationOrDocumentSymbol>();

    private readonly ILogger logger;
    private readonly IDocumentDatabase documents;

    public DafnyFoldingRangeHandler(ILogger<DafnyDocumentSymbolHandler> logger, IDocumentDatabase documents) {
      this.logger = logger;
      this.documents = documents;
    }

    protected override FoldingRangeRegistrationOptions CreateRegistrationOptions(FoldingRangeCapability capability, ClientCapabilities clientCapabilities) {
      return new FoldingRangeRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public async override Task<Container<FoldingRange>?> Handle(FoldingRangeRequestParam request, CancellationToken cancellationToken) {
      var document = await documents.GetDocumentAsync(request.TextDocument);
      if (document == null) {
        logger.LogWarning("symbols requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return null;
      }
      var visitor = new LspFoldingRangeGeneratingVisitor(document.SymbolTable, cancellationToken);
      return visitor.Visit(document.SymbolTable.CompilationUnit).ToArray();
    }
  }
}
