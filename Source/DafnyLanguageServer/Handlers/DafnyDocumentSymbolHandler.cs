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
    private static readonly SymbolInformationOrDocumentSymbol[] EmptySymbols = Array.Empty<SymbolInformationOrDocumentSymbol>();

    private readonly ILogger logger;
    private readonly IProjectDatabase projects;

    public DafnyDocumentSymbolHandler(ILogger<DafnyDocumentSymbolHandler> logger, IProjectDatabase projects) {
      this.logger = logger;
      this.projects = projects;
    }

    protected override DocumentSymbolRegistrationOptions CreateRegistrationOptions(DocumentSymbolCapability capability, ClientCapabilities clientCapabilities) {
      return new DocumentSymbolRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public override async Task<SymbolInformationOrDocumentSymbolContainer> Handle(DocumentSymbolParams request, CancellationToken cancellationToken) {
      var document = await projects.GetResolvedDocumentAsync(request.TextDocument);
      if (document == null) {
        logger.LogWarning("symbols requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return EmptySymbols;
      }
      var visitor = new LspSymbolGeneratingVisitor(document.SignatureAndCompletionTable, cancellationToken);
      var symbols = visitor.Visit(document.SignatureAndCompletionTable.CompilationUnit)
        .Select(symbol => new SymbolInformationOrDocumentSymbol(symbol))
        .ToArray();
      return symbols;
    }
  }
}
