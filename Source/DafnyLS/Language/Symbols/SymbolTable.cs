using IntervalTree;
using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Threading;
using AstElement = System.Object;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Represents the symbol table
  /// </summary>
  internal class SymbolTable {
    private readonly CompilationUnit _compilationUnit;
    private readonly IDictionary<AstElement, ILocalizableSymbol> _declarations = new Dictionary<AstElement, ILocalizableSymbol>();
    private readonly IIntervalTree<Position, ILocalizableSymbol> _symbolLookup = new IntervalTree<Position, ILocalizableSymbol>();

    private SymbolTable(CompilationUnit compilationUnit) {
      _compilationUnit = compilationUnit;
    }

    /// <summary>
    /// Initializes a new symbol table with the given compilation unit.
    /// </summary>
    /// <param name="compilationUnit"></param>
    /// <returns></returns>
    public static SymbolTable CreateFrom(CompilationUnit compilationUnit, CancellationToken cancellationToken) {
      var symbolTable = new SymbolTable(compilationUnit);
      foreach(var symbol in compilationUnit.GetAllDescendantsAndSelf().OfType<ILocalizableSymbol>()) {
        cancellationToken.ThrowIfCancellationRequested();
        symbolTable.RegisterDeclaration(symbol.Node, symbol);
      }
      return symbolTable;
    }

    private void RegisterDeclaration(AstElement node, ILocalizableSymbol symbol) {
      _declarations.Add(node, symbol);
    }

    public void LinkDesignatorToken(IToken token, ISymbol symbol) {
      if(symbol is ILocalizableSymbol localizableSymbol) {
        var range = localizableSymbol.GetHoverRange();
        _symbolLookup.Add(range.Start, range.End, localizableSymbol);
      }
    }

    /// <summary>
    /// Tries to get a symbol at the specified location.
    /// </summary>
    /// <param name="position">The requested position.</param>
    /// <param name="symbol">The symbol that could be identified at the given position, or <c>null</c> if no symbol could be identified.</param>
    /// <returns><c>true</c> if a symbol was found, otherwise <c>false</c>.</returns>
    public bool TryGetSymbolAt(Position position, [NotNullWhen(true)] out ILocalizableSymbol? symbol) {
      symbol = _symbolLookup.Query(position).SingleOrDefault();
      return symbol != null;
    }

    private class PositionComparer : Comparer<Position> {
      public override int Compare([AllowNull] Position x, [AllowNull] Position y) {
        if(x == null) {
          return y != null ? -1 : 0;
        } else if(y == null) {
          return 1;
        }
        int lineComparison = x.Line.CompareTo(y.Line);
        if(lineComparison != 0) {
          return lineComparison;
        }
        return x.Character.CompareTo(y.Character);
      }
    }
  }
}
