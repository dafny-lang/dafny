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

      var result = document.SymbolTable.GetDeclaration(request.Position);
      if (result == null) {
        logger.LogDebug("no symbol was found at {Position} in {Document}", request.Position, request.TextDocument);
        return new LocationOrLocationLinks();
      }
      return new[] { new LocationOrLocationLink(result) };
    }
  }
}
