using System;
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
  /// LSP handler responsible for project-wide symbol renames.
  /// </summary>
  public class DafnyRenameHandler : RenameHandlerBase {
    private readonly ILogger logger;
    private readonly IProjectDatabase projects;

    public DafnyRenameHandler(ILogger<DafnyRenameHandler> logger, IProjectDatabase projects) {
      this.logger = logger;
      this.projects = projects;
    }

    protected override RenameRegistrationOptions CreateRegistrationOptions(
      RenameCapability capability, ClientCapabilities clientCapabilities) {
      return new RenameRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public override async Task<WorkspaceEdit?> Handle(RenameParams request, CancellationToken cancellationToken) {
      if (string.IsNullOrWhiteSpace(request.NewName)) {
        // TODO: check identifiers more precisely
        return null;
      }

      var requestUri = request.TextDocument.Uri.ToUri();
      // Reject rename requests in implicit projects, because we might not find all references within the codebase,
      // so a partial rename may result in breaking the codebase
      if (!(await projects.GetProject(requestUri)).UsesProjectFile) {
        throw new Exception("Renaming support requires --project-mode and a Dafny project file (dfyconfig.toml)");
      }

      var state = await projects.GetResolvedDocumentAsyncInternal(request.TextDocument);
      if (state == null) {
        logger.LogWarning("location requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return null;
      }

      var node = state.SymbolTable.GetDeclarationNode(requestUri, request.Position);
      if (node == null || node.NavigationRange.StartToken.val == request.NewName) {
        return null;
      }

      var declaration = SymbolTable.NodeToLocation(node);
      if (declaration == null) {
        return null;
      }

      var usages = state.SymbolTable.GetReferences(declaration.Uri.ToUri(), declaration.Range.Start);
      var changes = usages
        .Append(declaration)
        .GroupBy(location => location.Uri)
        .ToDictionary(
          uriLocations => uriLocations.Key,
          uriLocations => uriLocations.Select(location => new TextEdit {
            Range = location.Range,
            NewText = request.NewName,
          }));
      return new WorkspaceEdit {
        Changes = changes
      };
    }
  }
}
