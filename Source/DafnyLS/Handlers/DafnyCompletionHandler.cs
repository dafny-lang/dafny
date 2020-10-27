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

    // TODO when is this method called and for what?
    public override bool CanResolve(CompletionItem completionItem) {
      return false;
    }

    // TODO when is this method called and for what?
    public override Task<CompletionItem> Handle(CompletionItem request, CancellationToken cancellationToken) {
      return Task.FromResult(request);
    }

    public override Task<CompletionList> Handle(CompletionParams request, CancellationToken cancellationToken) {
      DafnyDocument? document;
      if(!_documents.TryGetDocument(request.TextDocument, out document)) {
        _logger.LogWarning("location requested for unloaded document {}", request.TextDocument.Uri);
        return Task.FromResult(new CompletionList());
      }
      return Task.FromResult(new CompletionProcessor(_logger, document, request, cancellationToken).Process());
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
        var position = GetLinePositionBeforeDot();
        if(position == null) {
          _logger.LogTrace("dot was placed at the start of a line");
          return new CompletionList();
        }
        // TODO maybe one of the members was successfully resolved before. This should be a more reliable source instead of trying to resolve it manually.
        var memberAccesses = GetMemberAccessChainBefore(position);
        if(memberAccesses.Length == 0) {
          _logger.LogDebug("could not resolve the member access chain in front of the dot");
          return new CompletionList();
        }
        return CreateCompletionListFromSymbols(GetSymbolsToSuggest(position, memberAccesses));
      }

      private IEnumerable<ISymbol> GetSymbolsToSuggest(Position position, string[] memberAccessChain) {
        var enclosingSymbol = _document.SymbolTable.GetEnclosingSymbol(position, _cancellationToken);
        ISymbol? currentDesignator;
        ISymbol? currentDesignatorType = null;
        for(int currentMemberAccess = 0; currentMemberAccess < memberAccessChain.Length; currentMemberAccess++) {
          _cancellationToken.ThrowIfCancellationRequested();
          string currentDesignatorName = memberAccessChain[currentMemberAccess];
          if(currentMemberAccess == 0) {
            if(currentDesignatorName == "this") {
              // This actually the type, but TryGetTypeOf respects the case that the symbol itself is already a type.
              currentDesignator = GetEnclosingClass(enclosingSymbol);
            } else {
              currentDesignator = GetAccessedSymbolOfEnclosingScopes(enclosingSymbol, currentDesignatorName);
            }
          } else {
            currentDesignator = FindSymbolWithName(currentDesignatorType!, currentDesignatorName);
          }
          if(currentDesignator == null || !_document.SymbolTable.TryGetTypeOf(currentDesignator, out currentDesignatorType)) {
            _logger.LogDebug("could not resolve the designator {} of the member access chain '{}'", currentMemberAccess, memberAccessChain);
            return Enumerable.Empty<ISymbol>();
          }
        }
        return currentDesignatorType?.Children ?? Enumerable.Empty<ISymbol>();
      }

      private ISymbol? GetAccessedSymbolOfEnclosingScopes(ISymbol scope, string identifier) {
        _cancellationToken.ThrowIfCancellationRequested();
        var symbol = FindSymbolWithName(scope, identifier);
        if(symbol == null && scope.Scope != null) {
          return GetAccessedSymbolOfEnclosingScopes(scope.Scope, identifier);
        }
        return symbol;
      }

      private ClassSymbol? GetEnclosingClass(ISymbol scope) {
        _cancellationToken.ThrowIfCancellationRequested();
        if(scope is ClassSymbol classSymbol) {
          return classSymbol;
        }
        return scope.Scope == null ? null : GetEnclosingClass(scope.Scope);
      }

      private ISymbol? FindSymbolWithName(ISymbol containingSymbol, string identifier) {
        // TODO Careful: The current implementation of the method/function symbols do not respect scopes fully. Therefore, there might be
        // multiple symbols with the same name (e.g. locals of nested scopes, parameters,).
        return containingSymbol.Children
          .WithCancellation(_cancellationToken)
          .Where(child => child.Identifier == identifier)
          .FirstOrDefault();
      }

      private string[] GetMemberAccessChainBefore(Position position) {
        var text = _document.Text.Text;
        var absolutePosition = position.ToAbsolutePosition(text, _cancellationToken);
        return new MemberAccessChainResolver(text, absolutePosition, _cancellationToken).ResolveFromBehind().Reverse().ToArray();
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
          .Where(symbol => !IsConstructor(symbol))
          .Select(CreateCompletionItem)
          .ToArray();
        return new CompletionList(completionItems);
      }

      private bool IsConstructor(ISymbol symbol) {
        return symbol is MethodSymbol method
          && method.Identifier == "_ctor";
      }

      private CompletionItem CreateCompletionItem(ISymbol symbol) {
        return new CompletionItem {
          Label = symbol.Identifier,
          Kind = GetCompletionKind(symbol),
          InsertText = GetCompletionText(symbol),
          Detail = (symbol as ILocalizableSymbol)?.GetDetailText(_cancellationToken)
        };
      }

      private CompletionItemKind GetCompletionKind(ISymbol symbol) {
        return symbol switch {
          ClassSymbol _ => CompletionItemKind.Class,
          MethodSymbol _ => CompletionItemKind.Method,
          FunctionSymbol _ => CompletionItemKind.Function,
          VariableSymbol _ => CompletionItemKind.Variable,
          FieldSymbol _ => CompletionItemKind.Field,
          _ => CompletionItemKind.Reference
        };
      }

      private string GetCompletionText(ISymbol symbol) {
        return symbol switch {
          MethodSymbol _ => $"{symbol.Identifier}(",
          FunctionSymbol _ => $"{symbol.Identifier}(",
          _ => symbol.Identifier
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
      private readonly CancellationToken _cancellationToken;

      private bool IsTabOrSpace => _text[_position] == ' ' || _text[_position] == '\t';
      private bool IsAtNewStatement => _text[_position] == '\r' || _text[_position] == '\n' || _text[_position] == ';';
      private bool IsIdentifierCharacter => char.IsLetterOrDigit(_text[_position]) || _text[_position] == '_'; // TODO any other characters that are allowed characters?
      private bool IsMemberAccessOperator => _text[_position] == '.';

      public MemberAccessChainResolver(string text, int endPosition, CancellationToken cancellationToken) {
        _text = text;
        _position = endPosition;
        _cancellationToken = cancellationToken;
      }

      public IEnumerable<string> ResolveFromBehind() {
        while(_position >= 0) {
          _cancellationToken.ThrowIfCancellationRequested();
          SkipTabsAndSpaces();
          if(IsAtNewStatement) {
            yield break;
          }
          // TODO method/function invocations and indexers are not supported yet. Maybe just skip to their identifier?
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
          _cancellationToken.ThrowIfCancellationRequested();
          _position--;
        }
      }

      private string ReadIdentifier() {
        int identifierEnd = _position + 1;
        while(_position >= 0 && IsIdentifierCharacter) {
          _cancellationToken.ThrowIfCancellationRequested();
          _position--;
        }
        return _text[(_position + 1)..identifierEnd];
      }
    }
  }
}
