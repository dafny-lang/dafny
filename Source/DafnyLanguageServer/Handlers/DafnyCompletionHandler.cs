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
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  public class DafnyCompletionHandler : CompletionHandlerBase {
    private readonly ILogger<DafnyCompletionHandler> logger;
    private readonly IProjectDatabase projects;
    private readonly ISymbolGuesser symbolGuesser;
    private DafnyOptions options;

    public DafnyCompletionHandler(ILogger<DafnyCompletionHandler> logger, IProjectDatabase projects,
      ISymbolGuesser symbolGuesser, DafnyOptions options) {
      this.logger = logger;
      this.projects = projects;
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
      var document = await projects.GetParsedDocumentNormalizeUri(request.TextDocument);
      if (document == null) {
        logger.LogWarning("location requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return new CompletionList();
      }
      return new CompletionProcessor(symbolGuesser, logger, document, request, cancellationToken, options).Process();
    }

    private class CompletionProcessor {
      private DafnyOptions options;
      private ILogger<DafnyCompletionHandler> logger;
      private readonly ISymbolGuesser symbolGuesser;
      private readonly IdeState state;
      private readonly CompletionParams request;
      private readonly CancellationToken cancellationToken;

      public CompletionProcessor(ISymbolGuesser symbolGuesser, ILogger<DafnyCompletionHandler> logger, IdeState state,
        CompletionParams request, CancellationToken cancellationToken, DafnyOptions options) {
        this.symbolGuesser = symbolGuesser;
        this.state = state;
        this.request = request;
        this.cancellationToken = cancellationToken;
        this.options = options;
        this.logger = logger;
      }

      public CompletionList Process() {
        if (IsDotExpression()) {
          return CreateDotCompletionList();
        }

        if (logger.IsEnabled(LogLevel.Trace)) {
          var program = (Program)state.Program;
          var writer = new StringWriter();
          var printer = new Printer(writer, DafnyOptions.Default);
          printer.PrintProgram(program, true);
          logger.LogTrace($"Program:\n{writer}");
        }
        logger.LogDebug($"Completion not on a dot expression for {request.TextDocument.Uri}, version {state.Version}");
        return new CompletionList();
      }

      private bool IsDotExpression() {
        var node = state.Program.FindNode<INode>(request.TextDocument.Uri.ToUri(), request.Position.ToDafnyPosition());
        return node?.RangeToken.EndToken.val == ".";
      }

      private CompletionList CreateDotCompletionList() {
        IEnumerable<ILegacySymbol> members;
        if (symbolGuesser.TryGetTypeBefore(state,
              request.TextDocument.Uri.ToUri(), GetDotPosition(), cancellationToken, out var typeSymbol)) {
          if (typeSymbol is TypeWithMembersSymbolBase typeWithMembersSymbol) {
            members = typeWithMembersSymbol.Members;
          } else {
            throw new InvalidOperationException($"received a type symbol of type {typeSymbol.GetType()}, but expected a ClassSymbol");
          }
        } else {
          members = Enumerable.Empty<ILegacySymbol>();
        }
        return CreateCompletionListFromSymbols(members);
      }

      private Position GetDotPosition() {
        return new Position(request.Position.Line, request.Position.Character - 1);
      }

      private CompletionList CreateCompletionListFromSymbols(IEnumerable<ILegacySymbol> symbols) {
        var completionItems = symbols.WithCancellation(cancellationToken)
          .Where(symbol => !IsConstructor(symbol))
          .Select(CreateCompletionItem)
          .ToArray();
        return new CompletionList(completionItems);
      }

      private static bool IsConstructor(ILegacySymbol symbol) {
        return symbol is MethodSymbol method && method.Name == "_ctor";
      }

      private CompletionItem CreateCompletionItem(ILegacySymbol symbol) {
        return new CompletionItem {
          Label = symbol.Name,
          Kind = GetCompletionKind(symbol),
          InsertText = GetCompletionText(symbol),
          Detail = (symbol as ILocalizableSymbol)?.GetDetailText(options, cancellationToken)
        };
      }

      private static CompletionItemKind GetCompletionKind(ILegacySymbol symbol) {
        return symbol switch {
          TypeWithMembersSymbolBase _ => CompletionItemKind.Class,
          MethodSymbol _ => CompletionItemKind.Method,
          FunctionSymbol _ => CompletionItemKind.Function,
          VariableSymbol _ => CompletionItemKind.Variable,
          FieldSymbol _ => CompletionItemKind.Field,
          _ => CompletionItemKind.Reference
        };
      }

      private static string GetCompletionText(ILegacySymbol symbol) {
        return symbol.Name;
      }
    }
  }
}
