using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Represents a resolved symbol.
  /// </summary>
  public abstract class Symbol : ISymbol {

    /// <summary>
    /// Helper to convert a potentially null symbol to a list of symbols
    /// </summary>
    public static IEnumerable<TSymbol> AsEnumerable<TSymbol>(TSymbol? symbol) where TSymbol : ISymbol {
      return symbol != null ? new[] { symbol } : Enumerable.Empty<TSymbol>();
    }

    /// <summary>
    /// Gets the name of the symbol. The string is empty if the symbol does not have any name.
    /// </summary>
    public string Name { get; }

    /// <summary>
    /// Gets all children of the current symbol.
    /// </summary>
    public virtual IEnumerable<ISymbol> Children => Enumerable.Empty<ISymbol>();

    /// <summary>
    /// Gets the symbol representing the enclosing scope, <c>null</c> if no other symbol.
    /// </summary>
    public ISymbol? Scope { get; }

    public Symbol(ISymbol? scope, string name) {
      Scope = scope;
      Name = name;
    }

    public abstract TResult Accept<TResult>(ISymbolVisitor<TResult> visitor);
  }
}
