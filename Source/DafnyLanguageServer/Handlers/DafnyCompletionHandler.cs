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
      return new CompletionProcessor(symbolGuesser, logger, document, request, cancellationToken, options, await projects.GetProjectManager(request.TextDocument.Uri)).Process();
    }

    private class CompletionProcessor {
      private DafnyOptions options;
      private ILogger<DafnyCompletionHandler> logger;
      private readonly ISymbolGuesser symbolGuesser;
      private readonly IdeState state;
      private readonly CompletionParams request;
      private readonly CancellationToken cancellationToken;
      private readonly ProjectManager? projectManager;

      public CompletionProcessor(ISymbolGuesser symbolGuesser, ILogger<DafnyCompletionHandler> logger, IdeState state,
        CompletionParams request, CancellationToken cancellationToken, DafnyOptions options,
        ProjectManager? projectManager) {
        this.symbolGuesser = symbolGuesser;
        this.state = state;
        this.request = request;
        this.cancellationToken = cancellationToken;
        this.options = options;
        this.logger = logger;
        this.projectManager = projectManager;
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

      private static string GetLastTwoCharactersBeforePositionIncluded(TextReader fileContent, DafnyPosition position)
      {
        // To track the last two characters
        char? prevChar = null;
        char? currentChar = null;

        // Read line by line
        for (int lineNum = 0; lineNum <= position.Line; lineNum++)
        {
          string? line = fileContent.ReadLine();
          if (line == null)
          {
            throw new InvalidOperationException("Reached end of file before finding the specified line.");
          }

          // If we are on the line of the specified position, handle the partial line case
          if (lineNum == position.Line)
          {
            int columnIndex = position.Column - 1; // Convert 1-based to 0-based index
            for (int i = 0; i <= columnIndex; i++)
            {
              prevChar = currentChar;
              currentChar = line[i];
            }
            break;
          }
          else
          {
            // Otherwise, track the last two characters of this full line (including newline)
            foreach (char c in line + '\n')  // Include '\n' for line end tracking
            {
              prevChar = currentChar;
              currentChar = c;
            }
          }
        }

        // Handle case where fewer than 2 characters are available
        if (prevChar == null)
        {
          return currentChar?.ToString() ?? "";
        }
        return $"{prevChar}{currentChar}";
      }
      
      private bool IsDotExpression() {
        var node = state.Program.FindNode<INode>(request.TextDocument.Uri.ToUri(), request.Position.ToDafnyPosition());
        return node?.RangeToken.EndToken.val == ".";
      }

      private bool IsAtAttribute() {
        var position = request.Position.ToDafnyPosition();
        if (projectManager == null) {
          return false;
        }
        var fileContent = projectManager.ReadFile(request.TextDocument.Uri.ToUri());
        var lastTwoChars = GetLastTwoCharactersBeforePositionIncluded(fileContent, position);
        var isAtAttribute =
          lastTwoChars == "@" ||
          lastTwoChars.Length >= 2 && lastTwoChars[1] == '@' && char.IsWhiteSpace(lastTwoChars[0]);
        return isAtAttribute;
      }
      
      private CompletionList CreateAtAttributeCompletionList() {
        var completionItems = new List<string>() {
          "IsolateAssertions", // TODO: Put this list in Dafny Core
          "TailRecursion"
        }.Select(CreateCompletionItem);
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
          InsertText = attributeName, // TODO: Parentheses
          Detail = "" // TODO: Details of attribute name
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
