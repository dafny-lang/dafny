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

    public DafnyCompletionHandler(ILogger<DafnyCompletionHandler> logger, IDocumentDatabase documents, ISymbolGuesser symbolGuesser) {
      this.logger = logger;
      this.documents = documents;
      this.symbolGuesser = symbolGuesser;
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

    public async override Task<CompletionList> Handle(CompletionParams request, CancellationToken cancellationToken) {
      var document = await documents.GetDocumentAsync(request.TextDocument);
      if (document == null) {
        logger.LogWarning("location requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return new CompletionList();
      }
      return new CompletionProcessor(symbolGuesser, document, request, cancellationToken).Process();
    }

    private class CompletionProcessor {
      private readonly ISymbolGuesser symbolGuesser;
      private readonly DafnyDocument document;
      private readonly CompletionParams request;
      private readonly CancellationToken cancellationToken;

      public CompletionProcessor(ISymbolGuesser symbolGuesser, DafnyDocument document, CompletionParams request, CancellationToken cancellationToken) {
        this.symbolGuesser = symbolGuesser;
        this.document = document;
        this.request = request;
        this.cancellationToken = cancellationToken;
      }

      public CompletionList Process() {
        if (GetTriggerCharacter() == ".") {
          return CreateDotCompletionList();
        }
        return new CompletionList();
      }

      private string GetTriggerCharacter() {
        // Cannot use _request.Context.TriggerCharacter at this time, since _request.Context appears to be always null.
        var documentText = document.Text.Text;
        int absolutePosition = request.Position.ToAbsolutePosition(documentText, cancellationToken) - 1;
        return documentText[absolutePosition].ToString();
      }

      private CompletionList CreateDotCompletionList() {
        IEnumerable<ISymbol> members;
        if (symbolGuesser.TryGetTypeBefore(document, GetDotPosition(), cancellationToken, out var typeSymbol)) {
          if (typeSymbol is TypeWithMembersSymbolBase typeWithMembersSymbol) {
            members = typeWithMembersSymbol.Members;
          } else {
            // TODO This should never happen at this time.
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
          Detail = (symbol as ILocalizableSymbol)?.GetDetailText(cancellationToken)
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
