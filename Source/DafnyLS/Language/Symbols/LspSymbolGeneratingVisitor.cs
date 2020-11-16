﻿using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Visitor responsible to generate the LSP symbol representation.
  /// </summary>
  public class LspSymbolGeneratingVisitor : ISymbolVisitor<IEnumerable<DocumentSymbol>> {
    private readonly SymbolTable _symbolTable;
    private readonly CancellationToken _cancellationToken;

    public LspSymbolGeneratingVisitor(SymbolTable symbolTable, CancellationToken cancellationToken) {
      _symbolTable = symbolTable;
      _cancellationToken = cancellationToken;
    }

    private bool IsPartOfEntryDocument(Boogie.IToken token) {
      // Tokens with line=0 usually represent a default/implicit class/module/etc. We do not want
      // to show these in the symbol listing.
      return token.line != 0 && _symbolTable.CompilationUnit.Program.IsPartOfEntryDocument(token);
    }

    public IEnumerable<DocumentSymbol> Visit(ISymbol symbol) {
      _cancellationToken.ThrowIfCancellationRequested();
      return symbol.Accept(this);
    }

    public IEnumerable<DocumentSymbol> Visit(CompilationUnit compilationUnit) {
      return compilationUnit.Children.SelectMany(Visit).ToArray();
    }

    public IEnumerable<DocumentSymbol> Visit(ModuleSymbol moduleSymbol) {
      return CreateSymbols(moduleSymbol, moduleSymbol.Declaration.tok, SymbolKind.Module);
    }

    public IEnumerable<DocumentSymbol> Visit(ClassSymbol classSymbol) {
      return CreateSymbols(classSymbol, classSymbol.Declaration.tok, SymbolKind.Class);
    }

    public IEnumerable<DocumentSymbol> Visit(ValueTypeSymbol valueTypeSymbol) {
      return CreateSymbols(valueTypeSymbol, valueTypeSymbol.Declaration.tok, SymbolKind.Struct);
    }

    public IEnumerable<DocumentSymbol> Visit(FieldSymbol fieldSymbol) {
      return CreateSymbols(fieldSymbol, fieldSymbol.Declaration.tok, SymbolKind.Field);
    }

    public IEnumerable<DocumentSymbol> Visit(FunctionSymbol functionSymbol) {
      return CreateSymbols(functionSymbol, functionSymbol.Declaration.tok, SymbolKind.Function);
    }

    public IEnumerable<DocumentSymbol> Visit(MethodSymbol methodSymbol) {
      return CreateSymbols(methodSymbol, methodSymbol.Declaration.tok, SymbolKind.Method);
    }

    public IEnumerable<DocumentSymbol> Visit(VariableSymbol variableSymbol) {
      return CreateSymbols(variableSymbol, variableSymbol.Declaration.Tok, SymbolKind.Variable);
    }

    public IEnumerable<DocumentSymbol> Visit(ScopeSymbol scopeSymbol) {
      return scopeSymbol.Children.SelectMany(Visit);
    }

    private IEnumerable<DocumentSymbol> CreateSymbols(ILocalizableSymbol symbol, Boogie.IToken token, SymbolKind kind) {
      var children = symbol.Children.SelectMany(Visit);
      if(!IsPartOfEntryDocument(token)) {
        return children;
      }
      var documentSymbol = new DocumentSymbol {
        Name = symbol.Name,
        Kind = kind,
        Detail = symbol.GetDetailText(_cancellationToken),
        Children = children.ToArray()
      };
      if(_symbolTable.TryGetLocationOf(symbol, out var location)) {
        documentSymbol.Range = location.Declaration;
        documentSymbol.SelectionRange = location.Name;
      }
      return new[] { documentSymbol };
    }
  }
}
