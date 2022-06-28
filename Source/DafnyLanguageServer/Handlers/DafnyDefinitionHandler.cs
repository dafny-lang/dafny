using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  /// <summary>
  /// LSP handler responsible to resolve the location of a designator at the specified position.
  /// </summary>
  public class DafnyDefinitionHandler : DefinitionHandlerBase {
    private readonly ILogger logger;
    private readonly IDocumentDatabase documents;

    public DafnyDefinitionHandler(ILogger<DafnyDefinitionHandler> logger, IDocumentDatabase documents) {
      this.logger = logger;
      this.documents = documents;
    }
    protected override DefinitionRegistrationOptions CreateRegistrationOptions(DefinitionCapability capability, ClientCapabilities clientCapabilities) {
      return new DefinitionRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public override async Task<LocationOrLocationLinks> Handle(DefinitionParams request, CancellationToken cancellationToken) {
      var document = await documents.GetResolvedDocumentAsync(request.TextDocument);
      if (document == null) {
        logger.LogWarning("location requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return new LocationOrLocationLinks();
      }
      if (!document.SymbolTable.TryGetSymbolAt(request.Position, out var symbol)) {
        logger.LogDebug("no symbol was found at {Position} in {Document}", request.Position, request.TextDocument);
        return new LocationOrLocationLinks();
      }
      var location = GetLspLocation(document, symbol);
      if (location == null) {
        logger.LogDebug("failed to resolve the location of the symbol {SymbolName} at {Position} in {Document}",
          symbol.Name, request.Position, request.TextDocument);
        return new LocationOrLocationLinks();
      }
      return new[] { location };
    }

    private static LocationOrLocationLink? GetLspLocation(DafnyDocument document, ISymbol symbol) {
      if (document.SymbolTable.TryGetLocationOf(symbol, out var location)) {
        return new Location {
          Uri = location.Uri,
          Range = location.Name
        };
      }
      return null;
    }
  }
}
