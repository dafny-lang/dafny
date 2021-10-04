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

    private IEnumerable<Diagnostic> GetGhostsForDesignators(SymbolTable symbolTable, CancellationToken cancellationToken) {
      if(!options.FadeDeclarations) {
        yield break;
      }
      foreach (var entry in symbolTable.LookupTree) {
        cancellationToken.ThrowIfCancellationRequested();
        var range = new Range(entry.From, entry.To);
        var symbol = entry.Value;
        switch (symbol) {
          case VariableSymbol variable when IsGhostOfEntryDocument(variable, symbolTable):
            yield return CreateVariableDiagnostic(range);
            break;
          case FunctionSymbol function when IsGhostOfEntryDocument(function, symbolTable):
            yield return CreateFunctionDiagnostic(range);
            break;
        }
      }
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
            yield return CreateFunctionDiagnostic(new Range(function.Declaration.tok.GetLspPosition(), function.Declaration.BodyEndTok.GetLspPosition()));
            break;
        }
      }
    }

    private static bool IsGhostOfEntryDocument(VariableSymbol variable, SymbolTable symbolTable) {
      return variable.Declaration.IsGhost
        && symbolTable.CompilationUnit.Program.IsPartOfEntryDocument(variable.Declaration.Tok);
    }

    private static bool IsGhostOfEntryDocument(FunctionSymbol function, SymbolTable symbolTable) {
      return function.Declaration.IsGhost
        && symbolTable.CompilationUnit.Program.IsPartOfEntryDocument(function.Declaration.tok);
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
