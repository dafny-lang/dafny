using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// A table containing the symbols of a dafny syntax tree.
  /// </summary>
  internal class SymbolTable {
    /// <summary>
    /// Gets the parent symbol table (i.e., the table of the enclosing scope). If there is no enclosing scope, the value is <c>null</c>.
    /// </summary>
    public SymbolTable? Parent { get; }

    /// <summary>
    /// Gets the directly nested symbol tables of this symbol table.
    /// </summary>
    public ISet<SymbolTable> Children { get; } = new HashSet<SymbolTable>();

    private readonly ISet<ISymbol> _symbols = new HashSet<ISymbol>();

    public SymbolTable(SymbolTable? parent = default) {
      Parent = parent;
    }

    /// <summary>
    /// Creates a new child symbol table and stores it in the <see cref="Children"/> property.
    /// </summary>
    /// <returns>The created child symbol tab.e</returns>
    public SymbolTable NewChild() {
      var child = new SymbolTable(this);
      Children.Add(child);
      return child;
    }

    /// <summary>
    /// Registers the given symbol as its declaration.
    /// </summary>
    /// <param name="symbol">The symbol to register.</param>
    public void Register(ISymbol symbol) {
      _symbols.Add(symbol);
    }

    /// <summary>
    /// Gets all symbols of this table and its children tables. The symbols of this table are returned first.
    /// </summary>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>All symbols managed by this table and its children.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    public IEnumerable<ISymbol> AllSymbols(CancellationToken cancellationToken) {
      return _symbols.WithCancellation(cancellationToken)
        .Concat(Children.SelectMany(child => child.AllSymbols(cancellationToken)));
    }
  }
}
