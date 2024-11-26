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
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  public class DafnyCompletionHandler : CompletionHandlerBase {
    private readonly ILogger<DafnyCompletionHandler> logger;
    private readonly IProjectDatabase projects;
    private readonly LanguageServerFilesystem filesystem;
    private readonly ISymbolGuesser symbolGuesser;
    private DafnyOptions options;

    public DafnyCompletionHandler(ILogger<DafnyCompletionHandler> logger, IProjectDatabase projects,
      ISymbolGuesser symbolGuesser, DafnyOptions options, LanguageServerFilesystem filesystem) {
      this.logger = logger;
      this.projects = projects;
      this.symbolGuesser = symbolGuesser;
      this.options = options;
      this.filesystem = filesystem;
    }

    protected override CompletionRegistrationOptions CreateRegistrationOptions(CompletionCapability capability, ClientCapabilities clientCapabilities) {
      return new CompletionRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny"),
        ResolveProvider = false,
        TriggerCharacters = new Container<string>(".", "@")
      };
    }

    // Never called since "ResolveProvider" is set to false.
    public override Task<CompletionItem> Handle(CompletionItem request, CancellationToken cancellationToken) {
      // Never called since "ResolveProvider" is set to false.
      return Task.FromException<CompletionItem>(new InvalidOperationException("method not implemented"));
    }

    public override async Task<CompletionList> Handle(CompletionParams request, CancellationToken cancellationToken) {
      logger.LogDebug("Completion params received");
      var document = await projects.GetResolvedDocumentAsyncInternal(request.TextDocument);
      if (document == null) {
        logger.LogWarning("location requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return new CompletionList();
      }
      return new CompletionProcessor(symbolGuesser, logger, document, request, cancellationToken, options, filesystem).Process();
    }

    private class CompletionProcessor {
      private DafnyOptions options;
      private ILogger<DafnyCompletionHandler> logger;
      private readonly ISymbolGuesser symbolGuesser;
      private readonly IdeState state;
      private readonly CompletionParams request;
      private readonly CancellationToken cancellationToken;
      private readonly LanguageServerFilesystem filesystem;

      public CompletionProcessor(ISymbolGuesser symbolGuesser, ILogger<DafnyCompletionHandler> logger, IdeState state,
        CompletionParams request, CancellationToken cancellationToken, DafnyOptions options,
        LanguageServerFilesystem filesystem) {
        this.symbolGuesser = symbolGuesser;
        this.state = state;
        this.request = request;
        this.cancellationToken = cancellationToken;
        this.options = options;
        this.logger = logger;
        this.filesystem = filesystem;
      }

      public CompletionList Process() {
        if (IsDotExpression()) {
          return CreateDotCompletionList();
        }

        if (IsAtAttribute()) {
          return CreateAtAttributeCompletionList();
        }

        if (logger.IsEnabled(LogLevel.Trace)) {
          var program = (Program)state.ResolvedProgram!;
          var writer = new StringWriter();
          var printer = new Printer(writer, state.Input.Options);
          printer.PrintProgram(program, true);
          logger.LogTrace($"Program:\n{writer}");
        }
        logger.LogDebug($"Completion not on a dot expression for {request.TextDocument.Uri}, version {state.Version}");
        return new CompletionList();
      }

      private string GetLastTwoCharactersBeforePositionIncluded(TextBuffer text, DafnyPosition position) {
        var index = text.ToIndex(position.GetLspPosition());
        var indexTwoCharactersBefore = Math.Max(0, index - 2);
        if (index > text.Text.Length) {
          return "";
        }

        return text.Text.Substring(indexTwoCharactersBefore, index - indexTwoCharactersBefore);
      }

      private bool IsDotExpression() {
        var node = state.Program.FindNode<INode>(request.TextDocument.Uri.ToUri(), request.Position.ToDafnyPosition());
        return node?.Origin.EndToken.val == ".";
      }

      private bool IsAtAttribute() {
        var position = request.Position.ToDafnyPosition();
        var fileContent = filesystem.GetBuffer(request.TextDocument.Uri.ToUri());
        if (fileContent == null) {
          // Impossible case because this only happens if the file is not opened.
          return false;
        }
        var lastTwoChars = GetLastTwoCharactersBeforePositionIncluded(fileContent, position);
        var isAtAttribute =
          lastTwoChars == "@" ||
          lastTwoChars.Length >= 2 && lastTwoChars[1] == '@' && char.IsWhiteSpace(lastTwoChars[0]);
        return isAtAttribute;
      }

      private CompletionList CreateAtAttributeCompletionList() {
        var completionItems =
          Attributes.BuiltinAtAttributes.Select(b =>
            CreateCompletionItem(b.Name)
          ).ToList();
        return new CompletionList(completionItems);
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

      private CompletionItem CreateCompletionItem(string attributeName) {
        return new CompletionItem {
          Label = attributeName,
          Kind = CompletionItemKind.Constructor,
          InsertText = attributeName,
          Detail = ""
        };
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
