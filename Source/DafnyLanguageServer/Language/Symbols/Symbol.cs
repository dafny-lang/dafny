using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Represents a resolved symbol.
  /// </summary>
  public abstract class Symbol(ILegacySymbol? scope, string name) : ILegacySymbol {
    /// <summary>
    /// Gets the name of the symbol. The string is empty if the symbol does not have any name.
    /// </summary>
    public string Name { get; } = name;

    /// <summary>
    /// Gets all children of the current symbol.
    /// </summary>
    public virtual IEnumerable<ILegacySymbol> Children => [];

    /// <summary>
    /// Gets the symbol representing the enclosing scope, <c>null</c> if no other symbol.
    /// </summary>
    public ILegacySymbol? Scope { get; } = scope;

    public abstract TResult Accept<TResult>(ISymbolVisitor<TResult> visitor);
  }
}
