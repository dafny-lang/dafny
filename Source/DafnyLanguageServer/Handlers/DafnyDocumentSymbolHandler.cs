using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  /// <summary>
  /// LSP Synchronization handler for symbol based events, i.e. the client requests the symbols of the specified document.
  /// </summary>
  public class DafnyDocumentSymbolHandler : DocumentSymbolHandlerBase {
    private static readonly SymbolInformationOrDocumentSymbol[] EmptySymbols = Array.Empty<SymbolInformationOrDocumentSymbol>();

    private readonly ILogger logger;
    private readonly IProjectDatabase projects;
    private readonly DafnyOptions serverOptions;

    public DafnyDocumentSymbolHandler(ILogger<DafnyDocumentSymbolHandler> logger, IProjectDatabase projects, DafnyOptions serverOptions) {
      this.logger = logger;
      this.projects = projects;
      this.serverOptions = serverOptions;
    }

    protected override DocumentSymbolRegistrationOptions CreateRegistrationOptions(DocumentSymbolCapability capability, ClientCapabilities clientCapabilities) {
      return new DocumentSymbolRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public override async Task<SymbolInformationOrDocumentSymbolContainer> Handle(DocumentSymbolParams request, CancellationToken cancellationToken) {
      var state = await projects.GetParsedDocumentNormalizeUri(request.TextDocument);
      if (state == null) {
        logger.LogWarning("symbols requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return EmptySymbols;
      }

      var fileNodes = state.Program.FindNodesInUris(request.TextDocument.Uri.ToUri()).OfType<ISymbol>();
      return fileNodes.SelectMany(FromSymbol).Select(s => new SymbolInformationOrDocumentSymbol(s)).ToList();
    }

    private IEnumerable<DocumentSymbol> FromSymbol(ISymbol symbol) {
      var documentation = (symbol as IHasDocstring)?.GetDocstring(serverOptions) ?? "";
      var children = new List<DocumentSymbol>();
      if (symbol is IHasSymbolChildren hasSymbolChildren) {
        foreach (var child in hasSymbolChildren.ChildSymbols) {
          var childDocumentSymbols = FromSymbol(child);
          children.AddRange(childDocumentSymbols);
        }
      }

      if (!symbol.Kind.HasValue || string.IsNullOrEmpty(symbol.NavigationToken.val)) {
        return children;
      }

      var range = symbol.Origin.ToLspRange();
      return new DocumentSymbol[] {
        new() {
          Children = children,
          Name = symbol.NavigationToken.val,
          Detail = documentation,
          Range = range,
          Kind = symbol.Kind.Value,
          SelectionRange = symbol.NavigationToken == Token.NoToken ? range : symbol.NavigationToken.ToLspRange()
        }
      };
    }
  }
}
