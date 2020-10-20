using DafnyLS.Language;
using DafnyLS.Language.Symbols;
using DafnyLS.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Handlers {
  /// <summary>
  /// LSP handler responsible to resolve the location of a designator at the specified position.
  /// </summary>
  public class DafnyDefinitionHandler : DefinitionHandler {
    private readonly ILogger _logger;
    private readonly IDocumentDatabase _documents;

    public DafnyDefinitionHandler(ILogger<DafnyDefinitionHandler> logger, IDocumentDatabase documents) : base(CreateRegistrationOptions()) {
      _logger = logger;
      _documents = documents;
    }

    private static DefinitionRegistrationOptions CreateRegistrationOptions() {
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
      return Task.FromResult<LocationOrLocationLinks>(new[] { GetLspLocation(document, symbol) });
    }

    private LocationOrLocationLink GetLspLocation(DafnyDocument document, ILocalizableSymbol symbol) {
      return new Location {
        Uri = document.Uri,
        Range = symbol.GetHoverRange()
      };
    }
  }
}
