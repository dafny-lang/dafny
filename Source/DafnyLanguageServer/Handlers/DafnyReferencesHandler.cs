using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  /// <summary>
  /// LSP handler responsible for resolving the locations of references to the identifier at the specified position.
  /// </summary>
  public class DafnyReferencesHandler : ReferencesHandlerBase {
    private readonly ILogger logger;
    private readonly IProjectDatabase projects;

    public DafnyReferencesHandler(ILogger<DafnyReferencesHandler> logger, IProjectDatabase projects) {
      this.logger = logger;
      this.projects = projects;
    }

    protected override ReferenceRegistrationOptions CreateRegistrationOptions(
      ReferenceCapability capability, ClientCapabilities clientCapabilities) {
      return new ReferenceRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public override async Task<LocationContainer> Handle(ReferenceParams request, CancellationToken cancellationToken) {
      var state = await projects.GetResolvedDocumentAsyncInternal(request.TextDocument);
      if (state == null) {
        logger.LogWarning("location requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return new LocationContainer();
      }

      var requestUri = request.TextDocument.Uri.ToUri();
      var declaration = state.SymbolTable.GetDeclaration(requestUri, request.Position);
      return declaration == null
        ? new LocationContainer()
        : LocationContainer.From(state.SymbolTable.GetUsages(declaration.Uri.ToUri(), declaration.Range.Start));
    }
  }
}
