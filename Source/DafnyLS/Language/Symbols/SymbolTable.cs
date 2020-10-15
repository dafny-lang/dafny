using IntervalTree;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using AstElement = System.Object;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Represents the symbol table
  /// </summary>
  internal class SymbolTable {
    private readonly IIntervalTree<Position, ILocalizableSymbol> _symbolLookup;

    public SymbolTable(IIntervalTree<Position, ILocalizableSymbol> symbolLookup) {
      _symbolLookup = symbolLookup;
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
  }
}
