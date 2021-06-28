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
    private readonly ILogger _logger;
    private readonly IDocumentDatabase _documents;

    public DafnyDefinitionHandler(ILogger<DafnyDefinitionHandler> logger, IDocumentDatabase documents) {
      _logger = logger;
      _documents = documents;
    }
    protected override DefinitionRegistrationOptions CreateRegistrationOptions(DefinitionCapability capability, ClientCapabilities clientCapabilities) {
      return new DefinitionRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public override Task<LocationOrLocationLinks> Handle(DefinitionParams request, CancellationToken cancellationToken) {
      DafnyDocument? document;
      if(!_documents.TryGetDocument(request.TextDocument, out document)) {
        _logger.LogWarning("location requested for unloaded document {}", request.TextDocument.Uri);
        return Task.FromResult(new LocationOrLocationLinks());
      }
      ILocalizableSymbol? symbol;
      if(!document.SymbolTable.TryGetSymbolAt(request.Position, out symbol)) {
        _logger.LogDebug("no symbol was found at {} in {}", request.Position, request.TextDocument);
        return Task.FromResult(new LocationOrLocationLinks());
      }
      var location = GetLspLocation(document, symbol);
      if(location == null) {
        _logger.LogDebug("failed to resolve the location of the symbol {} at {} in {}", symbol.Name, request.Position, request.TextDocument);
        return Task.FromResult(new LocationOrLocationLinks());
      }
      return Task.FromResult<LocationOrLocationLinks>(new[] { location });
    }

    private LocationOrLocationLink? GetLspLocation(DafnyDocument document, ISymbol symbol) {
      if(document.SymbolTable.TryGetLocationOf(symbol, out var location)) {
        return new Location {
          Uri = location.Uri,
          Range = location.Name
        };
      }
      return null;
    }
  }
}
