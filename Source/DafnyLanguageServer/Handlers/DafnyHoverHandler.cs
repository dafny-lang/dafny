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
  public class DafnyHoverHandler : HoverHandlerBase {
    // TODO add the range of the name to the hover.
    private readonly ILogger _logger;
    private readonly IDocumentDatabase _documents;

    public DafnyHoverHandler(ILogger<DafnyHoverHandler> logger, IDocumentDatabase documents) {
      _logger = logger;
      _documents = documents;
    }

    protected override HoverRegistrationOptions CreateRegistrationOptions(HoverCapability capability, ClientCapabilities clientCapabilities) {
      return new HoverRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public override Task<Hover?> Handle(HoverParams request, CancellationToken cancellationToken) {
      _logger.LogTrace("received hover request for {}", request.TextDocument);
      DafnyDocument? textDocument;
      if(!_documents.TryGetDocument(request.TextDocument, out textDocument)) {
        _logger.LogWarning("the document {} is not loaded", request.TextDocument);
        return Task.FromResult<Hover?>(null);
      }

      ILocalizableSymbol? symbol;
      if(!textDocument.SymbolTable.TryGetSymbolAt(request.Position, out symbol)) {
        _logger.LogDebug("no symbol was found at {} in {}", request.Position, request.TextDocument);
        return Task.FromResult<Hover?>(null);
      }
      return Task.FromResult<Hover?>(CreateHover(symbol, cancellationToken));
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
