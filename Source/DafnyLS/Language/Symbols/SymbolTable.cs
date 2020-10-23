using IntervalTree;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Represents the symbol table
  /// </summary>
  public class SymbolTable {
    // TODO Guard the properties from changes

    /// <summary>
    /// Gets the interval tree backing this symbol table. Do not modify this instance.
    /// </summary>
    internal IIntervalTree<Position, ILocalizableSymbol> LookupTree { get; }

    /// <summary>
    /// Gets the dictionary allowing to resolve the location of a specified symbol. Do not modify this instance.
    /// </summary>
    internal IDictionary<ISymbol, SymbolLocation> Locations;

    public bool Resolved { get; }

    public SymbolTable(IDictionary<ISymbol, SymbolLocation> locations, IIntervalTree<Position, ILocalizableSymbol> symbolLookup, bool symbolsResolved) {
      Locations = locations;
      LookupTree = symbolLookup;
      Resolved = symbolsResolved;
    }

    /// <summary>
    /// Tries to get a symbol at the specified location.
    /// </summary>
    /// <param name="position">The requested position.</param>
    /// <param name="symbol">The symbol that could be identified at the given position, or <c>null</c> if no symbol could be identified.</param>
    /// <returns><c>true</c> if a symbol was found, otherwise <c>false</c>.</returns>
    public bool TryGetSymbolAt(Position position, [NotNullWhen(true)] out ILocalizableSymbol? symbol) {
      symbol = LookupTree.Query(position).SingleOrDefault();
      return symbol != null;
    }

    /// <summary>
    /// Tries to get the location of the given symbol.
    /// </summary>
    /// <param name="position">The symbol to get the location of.</param>
    /// <param name="location">The current location of the specified symbol, or <c>null</c> if no location of the given symbol is known.</param>
    /// <returns><c>true</c> if a location was found, otherwise <c>false</c>.</returns>
    public bool TryGetLocationOf(ISymbol symbol, [NotNullWhen(true)] out SymbolLocation? location) {
      return Locations.TryGetValue(symbol, out location);
    }
  }
}
