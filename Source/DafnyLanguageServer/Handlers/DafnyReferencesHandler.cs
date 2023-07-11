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

      var declaration = document.SymbolTable.GetDeclaration(request.Position);

      // The declaration graph is not reflexive, so the position might be on a declaration; return references to it
      if (declaration == null) {
        return document.SymbolTable.GetUsages(request.Position).ToArray();
      }

      // If the position is not on a declaration, return references to its declaration
      var definingDocument = declaration.Uri == document.Uri
        ? document
        : await projects.GetResolvedDocumentAsync(declaration.Uri);
      return definingDocument?.SymbolTable.GetUsages(declaration.Range.Start).ToArray() ?? new LocationContainer();
    }
  }
}
