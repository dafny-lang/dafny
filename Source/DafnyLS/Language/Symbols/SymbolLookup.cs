using IntervalTree;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// This class represents a lookup table to resolve the closest symbol when being queried with a location.
  /// </summary>
  public class SymbolLookup {
    private readonly IIntervalTree<Position, ILocalizableSymbol> _symbols;

    private SymbolLookup(IIntervalTree<Position, ILocalizableSymbol> symbols) {
      _symbols = symbols;
    }

    /// <summary>
    /// Creates a new symbol lookup based on the given symbol table.
    /// </summary>
    /// <param name="symbolTable">The symbol table to create a lookup of.</param>
    /// <param name="cancellationToken"></param>
    /// <returns>The initialized symbol lookup.</returns>
    public static SymbolLookup FromSymbolTable(CompilationUnit compilationUnit, CancellationToken cancellationToken) {
      var symbols = new IntervalTree<Position, ILocalizableSymbol>(new PositionComparer());
      foreach(var symbol in compilationUnit.GetAllDescendantsAndSelf().OfType<ILocalizableSymbol>()) {
        cancellationToken.ThrowIfCancellationRequested();
        var range = symbol.GetHoverRange();
        symbols.Add(range.Start, range.End, symbol);
      }
      return new SymbolLookup(symbols);
    }

    /// <summary>
    /// Tries to get a symbol at the specified location.
    /// </summary>
    /// <param name="position">The requested position.</param>
    /// <param name="symbol">The symbol that could be identified at the given position, or <c>null</c> if no symbol could be identified.</param>
    /// <returns><c>true</c> if a symbol was found, otherwise <c>false</c>.</returns>
    public bool TryGetSymbolAt(Position position, [NotNullWhen(true)] out ILocalizableSymbol? symbol) {
      symbol = _symbols.Query(position).SingleOrDefault();
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
