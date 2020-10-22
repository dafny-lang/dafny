using IntervalTree;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Diagnostics.CodeAnalysis;
using System.Linq;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Represents the symbol table
  /// </summary>
  public class SymbolTable {
    /// <summary>
    /// Gets the interval tree backing this symbol table. Do not modify this instance.
    /// </summary>
    // TODO Guard the lookup tree from changes
    internal IIntervalTree<Position, ILocalizableSymbol> LookupTree { get; }

    public bool Resolved { get; }

    public SymbolTable(IIntervalTree<Position, ILocalizableSymbol> symbolLookup, bool symbolsResolved) {
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
  }
}
