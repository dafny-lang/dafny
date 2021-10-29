using Microsoft.Dafny.LanguageServer.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Visitor responsible to generate the LSP foldable ranges.
  /// </summary>
  public class LspFoldingRangeGeneratingVisitor : ISymbolVisitor<IEnumerable<FoldingRange>> {
    private readonly SymbolTable symbolTable;
    private readonly CancellationToken cancellationToken;

    public LspFoldingRangeGeneratingVisitor(SymbolTable symbolTable, CancellationToken cancellationToken) {
      this.symbolTable = symbolTable;
      this.cancellationToken = cancellationToken;
    }

    private bool IsPartOfEntryDocument(Boogie.IToken token) {
      // Tokens with line=0 usually represent a default/implicit class/module/etc. We do not want
      // to show these in the symbol listing.
      return token.line != 0 && symbolTable.CompilationUnit.Program.IsPartOfEntryDocument(token);
    }

    public IEnumerable<FoldingRange> Visit(ISymbol symbol) {
      cancellationToken.ThrowIfCancellationRequested();
      return symbol.Accept(this);
    }

    public IEnumerable<FoldingRange> Visit(CompilationUnit compilationUnit) {
      return compilationUnit.Children.SelectMany(Visit).ToArray();
    }

    public IEnumerable<FoldingRange> Visit(ModuleSymbol moduleSymbol) {
      return CreateFoldingRangesOfEntryDocument(moduleSymbol, moduleSymbol.Declaration.tok);
    }

    public IEnumerable<FoldingRange> Visit(ClassSymbol classSymbol) {
      return CreateFoldingRangesOfEntryDocument(classSymbol, classSymbol.Declaration.tok);
    }

    public IEnumerable<FoldingRange> Visit(DataTypeSymbol dataTypeSymbol) {
      return CreateFoldingRangesOfEntryDocument(dataTypeSymbol, dataTypeSymbol.Declaration.tok);
    }

    public IEnumerable<FoldingRange> Visit(ValueTypeSymbol valueTypeSymbol) {
      return CreateFoldingRangesOfEntryDocument(valueTypeSymbol, valueTypeSymbol.Declaration.tok);
    }

    public IEnumerable<FoldingRange> Visit(FieldSymbol fieldSymbol) {
      return CreateFoldingRangesOfEntryDocument(fieldSymbol, fieldSymbol.Declaration.tok);
    }

    public IEnumerable<FoldingRange> Visit(FunctionSymbol functionSymbol) {
      return CreateFoldingRangesOfEntryDocument(functionSymbol, functionSymbol.Declaration.tok);
    }

    public IEnumerable<FoldingRange> Visit(MethodSymbol methodSymbol) {
      if (methodSymbol.Declaration.Body == null || !symbolTable.TryGetLocationOf(methodSymbol, out var location)) {
        return VisitChildren(methodSymbol);
      }
      if (methodSymbol.Returns.Count == 0 || !symbolTable.TryGetLocationOf(methodSymbol.Returns[^1], out var lastReturnLocation)) {
        return CreateFoldingRangesOfEntryDocument(methodSymbol, methodSymbol.Declaration.tok, location.Declaration);
      }
      var range = new Range(
        lastReturnLocation.Declaration.End,
        location.Declaration.End
      );
      return CreateFoldingRangesOfEntryDocument(methodSymbol, methodSymbol.Declaration.tok, range);
    }

    public IEnumerable<FoldingRange> Visit(VariableSymbol variableSymbol) {
      return CreateFoldingRangesOfEntryDocument(variableSymbol, variableSymbol.Declaration.Tok);
    }

    public IEnumerable<FoldingRange> Visit(ScopeSymbol scopeSymbol) {
      return CreateFoldingRangesOfEntryDocument(scopeSymbol, scopeSymbol.Declaration.Tok);
    }

    private IEnumerable<FoldingRange> CreateFoldingRangesOfEntryDocument(ILocalizableSymbol symbol, Boogie.IToken token) {
      if (!symbolTable.TryGetLocationOf(symbol, out var location)) {
        return VisitChildren(symbol);
      }
      return CreateFoldingRangesOfEntryDocument(symbol, token, location.Declaration);
    }

    private IEnumerable<FoldingRange> CreateFoldingRangesOfEntryDocument(ILocalizableSymbol symbol, Boogie.IToken token, Range range) {
      var children = VisitChildren(symbol);
      if (!IsPartOfEntryDocument(token)) {
        return children;
      }
      return children.Append(new FoldingRange {
        StartLine = range.Start.Line,
        StartCharacter = range.Start.Character,
        EndLine = range.End.Line,
        EndCharacter = range.End.Character
      });
    }

    private IEnumerable<FoldingRange> VisitChildren(ISymbol symbol) {
      return symbol.Children.SelectMany(Visit);
    }
  }
}
