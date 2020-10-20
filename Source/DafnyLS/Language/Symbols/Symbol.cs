using System.Collections.Generic;
using System.Linq;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Represents a resolved symbol.
  /// </summary>
  public abstract class Symbol : ISymbol {
    /// <summary>
    /// Gets the identifier of the symbol.
    /// </summary>
    public string Identifier { get; }

    /// <summary>
    /// Gets all children of the current symbol.
    /// </summary>
    public virtual IEnumerable<ISymbol> Children => Enumerable.Empty<ISymbol>();

    /// <summary>
    /// Gets the symbol representing the enclosing scope, <c>null</c> if no other symbol.
    /// </summary>
    public ISymbol? Scope { get; }

    public Symbol(ISymbol? scope, string identifier) {
      Scope = scope;
      Identifier = identifier;
    }

    public abstract TResult Accept<TResult>(ISymbolVisitor<TResult> visitor);
  }
}
