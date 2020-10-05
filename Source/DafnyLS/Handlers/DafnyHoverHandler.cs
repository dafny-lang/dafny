using DafnyLS.Language;
using DafnyLS.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Handlers {
  internal class DafnyHoverHandler : IHoverHandler {
    private readonly ILogger _logger;
    private readonly IDocumentDatabase _documents;

    public DafnyHoverHandler(ILogger<DafnyHoverHandler> logger, IDocumentDatabase documents) {
      _logger = logger;
      _documents = documents;
    }

    public HoverRegistrationOptions GetRegistrationOptions() {
      return new HoverRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public async Task<Hover> Handle(HoverParams request, CancellationToken cancellationToken) {
      _logger.LogTrace("received hover request for {}", request.TextDocument);
      DafnyDocument? textDocument;
      if(!_documents.TryGetDocument(request.TextDocument, out textDocument)) {
        _logger.LogWarning("the document {} is not loaded", request.TextDocument);
        return new Hover();
      }
      if(textDocument.SymbolTable.TryGetSymbolAt(request.Position, out var symbol)) {
        return new Hover {
          Contents = new MarkedStringsOrMarkupContent(
            new MarkupContent {
              Kind = MarkupKind.PlainText,
              Value = symbol.GetDetailText(cancellationToken)
            }
          )
        };
      }
      return new Hover();
    }

    public void SetCapability(HoverCapability capability) {
    }
  }
}
