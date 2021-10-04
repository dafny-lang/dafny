using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language {
  public class GhostStateDiagnosticCollector : IGhostStateDiagnosticCollector {
    private readonly GhostOptions options;

    public GhostStateDiagnosticCollector(IOptions<GhostOptions> options) {
      this.options = options.Value;
    }

    public IEnumerable<Diagnostic> GetGhostStateDiagnostics(SymbolTable symbolTable, CancellationToken cancellationToken) {
      return GetGhostsForDeclarations(symbolTable, cancellationToken)
        .Concat(GetGhostsForDesignators(symbolTable, cancellationToken));
    }

    private IEnumerable<Diagnostic> GetGhostsForDeclarations(SymbolTable symbolTable, CancellationToken cancellationToken) {
      if (!options.FadeDeclarations) {
        yield break;
      }
      foreach (var symbol in symbolTable.CompilationUnit.GetAllDescendantsAndSelf()) {
        cancellationToken.ThrowIfCancellationRequested();
        switch (symbol) {
          case VariableSymbol variable when IsGhostOfEntryDocument(variable, symbolTable):
            yield return CreateVariableDiagnostic(variable.Declaration.Tok.GetLspRange());
            break;
          case FunctionSymbol function when IsGhostOfEntryDocument(function, symbolTable):
            yield return CreateFunctionDiagnostic(GetDeclarationRange(function));
            break;
        }
      }
    }

    private static Range GetDeclarationRange(FunctionSymbol function) {
      var bodyEndPosition = function.Declaration.BodyEndTok.GetLspPosition();
      return new Range(
        function.Declaration.tok.GetLspPosition(),
        (bodyEndPosition.Line, bodyEndPosition.Character + 1)
      );
    }

    private static bool IsGhostOfEntryDocument(VariableSymbol variable, SymbolTable symbolTable) {
      return variable.Declaration.IsGhost
        && IsPartOfEntryDocumentAndNoMetadata(variable.Declaration.Tok, symbolTable);
    }

    private static bool IsGhostOfEntryDocument(FunctionSymbol function, SymbolTable symbolTable) {
      return function.Declaration.IsGhost
        && IsPartOfEntryDocumentAndNoMetadata(function.Declaration.tok, symbolTable);
    }

    private static bool IsPartOfEntryDocumentAndNoMetadata(Boogie.IToken token, SymbolTable symbolTable) {
      return token.line > 0
        && symbolTable.CompilationUnit.Program.IsPartOfEntryDocument(token);
    }

    private IEnumerable<Diagnostic> GetGhostsForDesignators(SymbolTable symbolTable, CancellationToken cancellationToken) {
      if (!options.FadeDesignators) {
        yield break;
      }
      foreach (var entry in symbolTable.LookupTree) {
        cancellationToken.ThrowIfCancellationRequested();
        var range = new Range(entry.From, entry.To);
        var symbol = entry.Value;
        switch (symbol) {
          case VariableSymbol variable when variable.Declaration.IsGhost:
            yield return CreateVariableDiagnostic(range);
            break;
          case FunctionSymbol function when function.Declaration.IsGhost:
            yield return CreateFunctionDiagnostic(range);
            break;
        }
      }
    }

    private static Diagnostic CreateFunctionDiagnostic(Range range) {
      return CreateDiagnostic(range, "Ghost function");
    }

    private static Diagnostic CreateVariableDiagnostic(Range range) {
      return CreateDiagnostic(range, "Ghost variable");
    }

    private static Diagnostic CreateDiagnostic(Range range, string message) {
      return new Diagnostic {
        Range = range,
        Tags = new[] { DiagnosticTag.Unnecessary },
        Message = message,
        Severity = DiagnosticSeverity.Hint
      };
    }
  }
}
