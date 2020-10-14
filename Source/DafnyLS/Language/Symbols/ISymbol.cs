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

    /// <summary>
    /// Applies double dispatching using the specified visitor instance.
    /// </summary>
    /// <typeparam name="TResult">The resulting value of the visit methods.</typeparam>
    /// <param name="visitor">The visitor to call the typed Visit method of.</param>
    /// <returns>The result of the actual visit method.</returns>
    TResult Accept<TResult>(ISymbolVisitor<TResult> visitor);
  }
}
