using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Represents a resolved symbol.
  /// </summary>
  public interface ILegacySymbol {
    /// <summary>
    /// Gets the name of the symbol. The string is empty if the symbol does not have any name.
    /// </summary>
    string Name { get; }

    /// <summary>
    /// Gets all children of the current symbol.
    /// </summary>
    IEnumerable<ILegacySymbol> Children { get; }

    /// <summary>
    /// Gets the symbol representing the enclosing scope, <c>null</c> if no other symbol.
    /// </summary>
    ILegacySymbol? Scope { get; }

    /// <summary>
    /// Applies double dispatching using the specified visitor instance.
    /// </summary>
    /// <typeparam name="TResult">The resulting value of the visit methods.</typeparam>
    /// <param name="visitor">The visitor to call the typed Visit method of.</param>
    /// <returns>The result of the actual visit method.</returns>
    TResult Accept<TResult>(ISymbolVisitor<TResult> visitor);
  }
}
