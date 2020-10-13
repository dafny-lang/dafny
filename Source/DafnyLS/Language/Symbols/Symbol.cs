using System.Collections.Generic;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Represents a resolved symbol.
  /// </summary>
  internal abstract class Symbol {
    /// <summary>
    /// Gets the identifier of the symbol.
    /// </summary>
    public string Identifier { get; }

    /// <summary>
    /// Gets the symbol representing the enclosing scope, <c>null</c> if no other symbol.
    /// </summary>
    public Symbol? Scope { get; }

    public Symbol(Symbol? scope, string identifier) {
      Scope = scope;
      Identifier = identifier;
    }

    /// <summary>
    /// Gets all descendants in pre-order, i.e., the current symbol is emitted before its children and their descendants.
    /// </summary>
    /// <returns>The symbol itself and all its descendants.</returns>
    public virtual IEnumerable<Symbol> GetAllDescendantsAndSelf() {
      yield return this;
    }
  }
}
