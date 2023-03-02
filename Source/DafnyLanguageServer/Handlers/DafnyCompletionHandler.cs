using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
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

namespace Microsoft.Dafny.LanguageServer.Handlers {
  public class DafnyCompletionHandler : CompletionHandlerBase {
    private readonly ILogger logger;
    private readonly IDocumentDatabase documents;
    private readonly ISymbolGuesser symbolGuesser;
    private DafnyOptions options;

    public DafnyCompletionHandler(ILogger<DafnyCompletionHandler> logger, IDocumentDatabase documents, 
      ISymbolGuesser symbolGuesser, DafnyOptions options) {
      this.logger = logger;
      this.documents = documents;
      this.symbolGuesser = symbolGuesser;
      this.options = options;
    }

    protected override CompletionRegistrationOptions CreateRegistrationOptions(CompletionCapability capability, ClientCapabilities clientCapabilities) {
      return new CompletionRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny"),
        ResolveProvider = false,
        TriggerCharacters = new Container<string>(".")
      };
    }

    // Never called since "ResolveProvider" is set to false.
    public override Task<CompletionItem> Handle(CompletionItem request, CancellationToken cancellationToken) {
      // Never called since "ResolveProvider" is set to false.
      return Task.FromException<CompletionItem>(new InvalidOperationException("method not implemented"));
    }

    public override async Task<CompletionList> Handle(CompletionParams request, CancellationToken cancellationToken) {
      logger.LogDebug("Completion params received");
      var document = await documents.GetResolvedDocumentAsync(request.TextDocument);
      if (document == null) {
        logger.LogWarning("location requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return new CompletionList();
      }
      logger.LogDebug($"Completion params retrieved document state with version {document.Version}");
      return new CompletionProcessor(symbolGuesser, document, request, cancellationToken, options).Process();
    }

    private class CompletionProcessor {
      private DafnyOptions options;
      private readonly ISymbolGuesser symbolGuesser;
      private readonly IdeState state;
      private readonly CompletionParams request;
      private readonly CancellationToken cancellationToken;

      public CompletionProcessor(ISymbolGuesser symbolGuesser, IdeState state, CompletionParams request, CancellationToken cancellationToken, DafnyOptions options) {
        this.symbolGuesser = symbolGuesser;
        this.state = state;
        this.request = request;
        this.cancellationToken = cancellationToken;
        this.options = options;
      }

      public CompletionList Process() {
        if (GetTriggerCharacter() == ".") {
          return CreateDotCompletionList();
        }
        return new CompletionList();
      }

      private string GetTriggerCharacter() {
        // Cannot use _request.Context.TriggerCharacter at this time, since _request.Context appears to be always null.
        var documentText = state.TextDocumentItem;
        int index = documentText.ToIndex(request.Position) - 1;
        return documentText.Text[index].ToString();
      }

      private CompletionList CreateDotCompletionList() {
        IEnumerable<ISymbol> members;
        if (symbolGuesser.TryGetTypeBefore(state, GetDotPosition(), cancellationToken, out var typeSymbol)) {
          if (typeSymbol is TypeWithMembersSymbolBase typeWithMembersSymbol) {
            members = typeWithMembersSymbol.Members;
          } else {
            throw new InvalidOperationException($"received a type symbol of type {typeSymbol.GetType()}, but expected a ClassSymbol");
          }
        } else {
          members = Enumerable.Empty<ISymbol>();
        }
        return CreateCompletionListFromSymbols(members);
      }

      private Position GetDotPosition() {
        return new Position(request.Position.Line, request.Position.Character - 1);
      }

      private CompletionList CreateCompletionListFromSymbols(IEnumerable<ISymbol> symbols) {
        var completionItems = symbols.WithCancellation(cancellationToken)
          .Where(symbol => !IsConstructor(symbol))
          .Select(CreateCompletionItem)
          .ToArray();
        return new CompletionList(completionItems);
      }

      private static bool IsConstructor(ISymbol symbol) {
        return symbol is MethodSymbol method
          && method.Name == "_ctor";
      }

      private CompletionItem CreateCompletionItem(ISymbol symbol) {
        return new CompletionItem {
          Label = symbol.Name,
          Kind = GetCompletionKind(symbol),
          InsertText = GetCompletionText(symbol),
          Detail = (symbol as ILocalizableSymbol)?.GetDetailText(options, cancellationToken)
        };
      }

      private static CompletionItemKind GetCompletionKind(ISymbol symbol) {
        return symbol switch {
          TypeWithMembersSymbolBase _ => CompletionItemKind.Class,
          MethodSymbol _ => CompletionItemKind.Method,
          FunctionSymbol _ => CompletionItemKind.Function,
          VariableSymbol _ => CompletionItemKind.Variable,
          FieldSymbol _ => CompletionItemKind.Field,
          _ => CompletionItemKind.Reference
        };
      }

      private static string GetCompletionText(ISymbol symbol) {
        return symbol.Name;
      }
    }
  }
}
