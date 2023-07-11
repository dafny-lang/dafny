using System.Linq;
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
      var document = await projects.GetResolvedDocumentAsync(request.TextDocument);
      if (document == null) {
        logger.LogWarning("location requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return new LocationContainer();
      }

      // If the position is not on a definition, return references to its definition
      var definition = document.SymbolTable.GetDeclaration(request.Position);
      if (definition != null) {
        return document.SymbolTable.GetUsages(definition.Range.Start).ToArray();
      }

      // The position might itself be a definition; return references to it
      var usages = document.SymbolTable.GetUsages(request.Position);
      return usages.ToArray();
    }
  }
}
