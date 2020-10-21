using DafnyLS.Language;
using DafnyLS.Language.Symbols;
using DafnyLS.Util;
using DafnyLS.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Handlers {
  public class DafnyCompletionHandler : CompletionHandler {
    private readonly ILogger _logger;
    private readonly IDocumentDatabase _documents;

    public DafnyCompletionHandler(ILogger<DafnyDefinitionHandler> logger, IDocumentDatabase documents) : base(CreateRegistrationOptions()) {
      _logger = logger;
      _documents = documents;
    }

    private static CompletionRegistrationOptions CreateRegistrationOptions() {
      return new CompletionRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny"),
        ResolveProvider = false,
        TriggerCharacters = new Container<string>(".")
      };
    }

    public override bool CanResolve(CompletionItem completionItem) {
      return false;
    }

    public override Task<CompletionList> Handle(CompletionParams request, CancellationToken cancellationToken) {
      DafnyDocument? document;
      if(!_documents.TryGetDocument(request.TextDocument, out document)) {
        _logger.LogWarning("location requested for unloaded document {}", request.TextDocument.Uri);
        return Task.FromResult(new CompletionList());
      }
      return Task.FromResult(new CompletionProcessor(_logger, document, request, cancellationToken).Process());
    }

    public override Task<CompletionItem> Handle(CompletionItem request, CancellationToken cancellationToken) {
      return Task.FromResult(request);
    }

    private class CompletionProcessor {
      private readonly ILogger _logger;
      private readonly DafnyDocument _document;
      private readonly CompletionParams _request;
      private readonly CancellationToken _cancellationToken;

      public CompletionProcessor(ILogger logger, DafnyDocument document, CompletionParams request, CancellationToken cancellationToken) {
        _logger = logger;
        _document = document;
        _request = request;
        _cancellationToken = cancellationToken;
      }

      public CompletionList Process() {
        if(GetTriggerCharacter() == ".") {
          return CreateDotCompletionList();
        }
        return new CompletionList();
      }

      private string GetTriggerCharacter() {
        // Cannot use _request.Context.TriggerCharacter at this time, since _request.Context appears to be always null.
        var documentText = _document.Text.Text;
        int absolutePosition = _request.Position.ToAbsolutePosition(documentText, _cancellationToken) - 1;
        return documentText[absolutePosition].ToString();
      }

      private CompletionList CreateDotCompletionList() {
        if(_document.SymbolTable.TryGetSymbolAt(GetPositionOfSymbolBefore(_request.Position), out var symbol)) {
          return CreateCompletionListFromSymbols(symbol.Children);
        }
        _logger.LogDebug("no symbol was found before {} in {} for dot completion", _request.Position, _request.TextDocument);
        return new CompletionList();
      }

      private static Position GetPositionOfSymbolBefore(Position position) {
        // The sent location is right after the . character. We want the symbol right before it.
        return new Position(position.Line, position.Character - 2);
      }

      private CompletionList CreateCompletionListFromSymbols(IEnumerable<ISymbol> symbols) {
        var completionItems = symbols.WithCancellation(_cancellationToken)
          .Select(CreateCompletionItem)
          .ToArray();
        return new CompletionList(completionItems);
      }

      private CompletionItem CreateCompletionItem(ISymbol symbol) {
        return new CompletionItem {
          Label = symbol.Identifier,
          Kind = CompletionItemKind.Reference,
          InsertText = symbol.Identifier,
          Detail = (symbol as ILocalizableSymbol)?.GetDetailText(_cancellationToken)
        };
      }
    }
  }
}
