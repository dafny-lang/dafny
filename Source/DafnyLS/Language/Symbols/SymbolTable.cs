using Microsoft.Boogie;
using System.Collections.Generic;
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

    private readonly IDictionary<string, ISymbol> _symbols = new Dictionary<string, ISymbol>();
    private readonly ISet<ReferenceSymbol> _references = new HashSet<ReferenceSymbol>();

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
      // TODO check dafny lang spec: Is it possible that multiple symbols in the same scope have the same name?
      //      For example, is it possible that a member method has the same name as a member field while being part of the same class?
      // Current assumption: It is not possible. Therefore, such occurences are treated as an error.
      _symbols.Add(symbol.Name, symbol);
    }

    /// <summary>
    /// Tries to register the given token as a reference to the symbol with the specified name.
    /// </summary>
    /// <param name="referencingToken">The token that should b registered as a reference to the symbol.</param>
    /// <param name="symbolName">The name of the symbol that the token is referencing.</param>
    /// <returns><c>true</c> if a symbol with the given name was found and registered, <c>false</c> otherwise.</returns>
    public bool TryRegisterReference(IToken referencingToken, string symbolName) {
      var resolvedSymbol = GetSymbolByName(symbolName);
      if(resolvedSymbol == null) {
        return false;
      }
      _references.Add(new ReferenceSymbol(referencingToken, resolvedSymbol));
      return true;
    }

    private ISymbol? GetSymbolByName(string symbolName) {
      if(_symbols.TryGetValue(symbolName, out var symbol)) {
        return symbol;
      }
      return Parent?.GetSymbolByName(symbolName);
    }

    /// <summary>
    /// Gets all symbols of this table and its children tables. The symbols of this table are returned first.
    /// </summary>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>All symbols managed by this table and its children.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    public IEnumerable<ISymbol> AllSymbols(CancellationToken cancellationToken) {
      return _symbols.Values
        .WithCancellation(cancellationToken)
        .Concat(Children.SelectMany(child => child.AllSymbols(cancellationToken)));
    }

    /// <summary>
    /// Gets all symbol references of this table and its children tables. The references of this table are returned first.
    /// </summary>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>All references managed by this table and its children.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    public IEnumerable<ReferenceSymbol> AllReferences(CancellationToken cancellationToken) {
      return _references
        .WithCancellation(cancellationToken)
        .Concat(Children.SelectMany(child => child.AllReferences(cancellationToken)));
    }
  }
}
