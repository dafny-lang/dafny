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
        /*if(_document.SymbolTable.TryGetSymbolAt(GetPositionOfSymbolBefore(_request.Position), out var symbol)) {
          return CreateCompletionListFromSymbols(symbol.Children);
        }
        _logger.LogDebug("no symbol was found before {} in {} for dot completion", _request.Position, _request.TextDocument);*/
        var position = GetLinePositionBeforeDot();
        if(position == null) {
          return new CompletionList();
        }
        // TODO maybe one of the members was successfully resolved before. This should be a more reliable source instead of trying to resolve it manually.
        var memberAccesses = GetMemberAccessChainBefore(position);
        return new CompletionList();
      }

      private string[] GetMemberAccessChainBefore(Position position) {
        var text = _document.Text.Text;
        var absolutePosition = position.ToAbsolutePosition(text, _cancellationToken);
        return new MemberAccessChainResolver(text, absolutePosition).ResolveFromBehind().Reverse().ToArray();
      }

      private Position? GetLinePositionBeforeDot() {
        var position = _request.Position;
        if(position.Character < 2) {
          return null;
        }
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

    // TODO This is a simple PoC for code suggestion that only works in a regular manner (tokenization).
    //      It should be refined in a context-free parser to generate a mini AST or something suitable that can better represent the actual syntax.
    //      In general, a speculative parser and semantic checker would be suitable to transition an existing semantic model.
    // TODO Instead of "parsing" when a completion was requested, it should be done when transitioning from one semantic model to another speculative one.
    //      This should simplify the completion implementation and unify other actions depending on the (speculative) semantic model.
    private class MemberAccessChainResolver {
      private readonly string _text;
      private int _position;

      private bool IsTabOrSpace => _text[_position] == ' ' || _text[_position] == '\t';
      private bool IsAtNewStatement => _text[_position] == '\r' || _text[_position] == '\n' || _text[_position] == ';';
      private bool IsIdentifierCharacter => char.IsLetterOrDigit(_text[_position]) || _text[_position] == '_'; // TODO any other characters that are allowed characters?
      private bool IsMemberAccessOperator => _text[_position] == '.';

      public MemberAccessChainResolver(string text, int endPosition) {
        _text = text;
        _position = endPosition;
      }

      public IEnumerable<string> ResolveFromBehind() {
        while(_position >= 0) {
          SkipTabsAndSpaces();
          if(IsAtNewStatement) {
            yield break;
          }
          // TODO method/function invocations not supported yet. Maybe just skip to their identifier?
          if(IsIdentifierCharacter) {
            yield return ReadIdentifier();
          } else {
            yield break;
          }
          SkipTabsAndSpaces();
          if(IsMemberAccessOperator) {
            _position--;
          } else {
            yield break;
          }
        }
      }

      private void SkipTabsAndSpaces() {
        while(_position >= 0 && IsTabOrSpace) {
          _position--;
        }
      }

      private string ReadIdentifier() {
        int identifierEnd = _position + 1;
        while(_position >= 0 && IsIdentifierCharacter) {
          _position--;
        }
        return _text[(_position + 1)..identifierEnd];
      }
    }
  }
}
