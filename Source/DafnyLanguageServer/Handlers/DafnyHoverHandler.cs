using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using OmniSharp.Extensions.JsonRpc.Server;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  public class DafnyHoverHandler : HoverHandlerBase {
    // TODO add the range of the name to the hover.
    private readonly ILogger logger;
    private readonly IDocumentDatabase documents;

    public DafnyHoverHandler(ILogger<DafnyHoverHandler> logger, IDocumentDatabase documents) {
      this.logger = logger;
      this.documents = documents;
    }

    protected override HoverRegistrationOptions CreateRegistrationOptions(HoverCapability capability, ClientCapabilities clientCapabilities) {
      return new HoverRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public async override Task<Hover?> Handle(HoverParams request, CancellationToken cancellationToken) {
      logger.LogTrace("received hover request for {Document}", request.TextDocument);
      var document = await documents.GetDocumentAsync(request.TextDocument);
      if (document == null) {
        logger.LogWarning("the document {Document} is not loaded", request.TextDocument);
        return null;
      }
      if (!document.SymbolTable.TryGetSymbolAt(request.Position, out var symbol)) {
        var hover = GetDiagnosticsHover(document, request.Position);
        if (hover != null) {
          return hover;
        }
        logger.LogDebug("no symbol was found at {Position} in {Document}", request.Position, request.TextDocument);
        return null;
      }
      return CreateHover(symbol, cancellationToken);
    }

    private static Hover? GetDiagnosticsHover(DafnyDocument document, Position position) {
      foreach (var nodeDiagnostic in document.VerificationNodeDiagnostic.Children) {
        if (nodeDiagnostic.Position.Line == position.Line + 1 &&
            nodeDiagnostic.Filename == document.Uri.GetFileSystemPath()) {
          var information = "**" + nodeDiagnostic.DisplayName + "** metrics:\n\n";
          information +=
              !nodeDiagnostic.Started ? "_Verification not started yet_"
              : !nodeDiagnostic.Finished ? "_Still verifying..._  \nTime: " + nodeDiagnostic.TimeSpent + "ms"
              : "Time: " + nodeDiagnostic.TimeSpent + "ms  \nResource: " + nodeDiagnostic.ResourceCount;
          return new Hover {
            Contents = new MarkedStringsOrMarkupContent(
              new MarkupContent {
                Kind = MarkupKind.Markdown,
                Value = $"{information}"
              }
            )
          };
        }
      }

      return null;
    }

    private static Hover CreateHover(ILocalizableSymbol symbol, CancellationToken cancellationToken) {
      return new Hover {
        Contents = new MarkedStringsOrMarkupContent(
          new MarkupContent {
            // TODO It appears that setting plaintext/markdown doesn't make a difference, at least in VSCode.
            Kind = MarkupKind.Markdown,
            Value = $"```dafny\n{symbol.GetDetailText(cancellationToken)}\n```"
          }
        )
      };
    }
  }
}
