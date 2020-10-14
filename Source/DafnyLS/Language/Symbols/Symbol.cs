using System.Collections.Generic;
using System.Linq;

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
    /// Gets all children of the current symbol.
    /// </summary>
    public virtual IEnumerable<Symbol> Children => Enumerable.Empty<Symbol>();

    /// <summary>
    /// Gets the symbol representing the enclosing scope, <c>null</c> if no other symbol.
    /// </summary>
    public Symbol? Scope { get; }

    public Symbol(Symbol? scope, string identifier) {
      Scope = scope;
      Identifier = identifier;
    }
  }
}
