using DafnyLS.Util;
using IntervalTree;
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
  public class SymbolTable {
    // TODO Guard the properties from changes
    public CompilationUnit CompilationUnit { get; }

    /// <summary>
    /// Gets the dictionary providing a mapping from an Ast Element to the symbol backing it.
    /// </summary>
    internal IDictionary<AstElement, ILocalizableSymbol> Declarations { get; }

    /// <summary>
    /// Gets the dictionary allowing to resolve the location of a specified symbol. Do not modify this instance.
    /// </summary>
    internal IDictionary<ISymbol, SymbolLocation> Locations { get; }

    /// <summary>
    /// Gets the interval tree backing this symbol table. Do not modify this instance.
    /// </summary>
    internal IIntervalTree<Position, ILocalizableSymbol> LookupTree { get; }

    public bool Resolved { get; }

    private readonly DafnyLangTypeResolver _typeResolver;

    public SymbolTable(
        CompilationUnit compilationUnit,
        IDictionary<AstElement, ILocalizableSymbol> declarations,
        IDictionary<ISymbol, SymbolLocation> locations,
        IIntervalTree<Position, ILocalizableSymbol> symbolLookup,
        bool symbolsResolved
    ) {
      CompilationUnit = compilationUnit;
      Declarations = declarations;
      Locations = locations;
      LookupTree = symbolLookup;
      Resolved = symbolsResolved;
      _typeResolver = new DafnyLangTypeResolver(declarations);

      // TODO IntervalTree goes out of sync after any change and "fixes" its state upon the first query. Replace it with another implementation that can be queried without potential side-effects.
      LookupTree.Query(new Position(0, 0));
    }

    /// <summary>
    /// Tries to get a symbol at the specified location.
    /// </summary>
    /// <param name="position">The requested position.</param>
    /// <param name="symbol">The symbol that could be identified at the given position, or <c>null</c> if no symbol could be identified.</param>
    /// <returns><c>true</c> if a symbol was found, otherwise <c>false</c>.</returns>
    /// <exception cref="System.InvalidOperationException">Thrown if there was one more symbol at the specified position. This should never happen, unless there was an error.</exception>
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

    /// <summary>
    /// Resolves the innermost symbol that encloses the given position.
    /// </summary>
    /// <param name="position">The position to get the innermost symbol of.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The innermost symbol at the specified position.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    public ISymbol GetEnclosingSymbol(Position position, CancellationToken cancellationToken) {
      // TODO use a suitable data-structure to resolve the locations efficiently.
      var comparer = new PositionComparer();
      ISymbol innerMostSymbol = CompilationUnit;
      var innerMostRange = new Range(new Position(0, 0), new Position(int.MaxValue, int.MaxValue));
      foreach(var (symbol, location) in Locations) {
        cancellationToken.ThrowIfCancellationRequested();
        var range = location.Declaration;
        if(IsEnclosedBy(comparer, innerMostRange, range) && IsInside(comparer, range, position)) {
          innerMostSymbol = symbol;
          innerMostRange = range;
        }
      }
      return innerMostSymbol;
    }

    private static bool IsEnclosedBy(PositionComparer comparer, Range current, Range tested) {
      return comparer.Compare(tested.Start, current.Start) >= 0
        && comparer.Compare(tested.End, current.End) <= 0;
    }

    private static bool IsInside(PositionComparer comparer, Range range, Position position) {
      return comparer.Compare(position, range.Start) >= 0
        && comparer.Compare(position, range.End) <= 0;
    }

    /// <summary>
    /// Tries to resolve the type of the given symbol.
    /// </summary>
    /// <param name="symbol">The symbol to get the type of.</param>
    /// <param name="type">The type of the symbol, or <c>null</c> if the type could not be resolved.</param>
    /// <returns><c>true</c> if the type was successfully resolved, otherwise <c>false</c>.</returns>
    public bool TryGetTypeOf(ISymbol symbol, [NotNullWhen(true)] out ISymbol? type) {
      var dafnyType = symbol switch {
        FieldSymbol field => field.Declaration.Type,
        VariableSymbol variable => variable.Declaration.Type,
        _ => null
      };
      if(dafnyType == null) {
        type = null;
        return false;
      }
      return _typeResolver.TryGetTypeSymbol(dafnyType, out type);
    }
  }
}
