using System.Collections.Generic;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Represents a resolved symbol.
  /// </summary>
  internal interface ISymbol {
    /// <summary>
    /// Gets the identifier of the symbol.
    /// </summary>
    string Identifier { get; }

    /// <summary>
    /// Gets all children of the current symbol.
    /// </summary>
    IEnumerable<ISymbol> Children { get; }

    /// <summary>
    /// Gets the symbol representing the enclosing scope, <c>null</c> if no other symbol.
    /// </summary>
    ISymbol? Scope { get; }
  }
}
