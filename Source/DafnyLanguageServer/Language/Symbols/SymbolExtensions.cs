using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Extension methods when working with the symbols of the language server.
  /// </summary>
  public static class SymbolExtensions {
    /// <summary>
    /// Recursively resolves (in pre-order) all the descendants of the given symbol including itself.
    /// </summary>
    /// <param name="symbol">The symbol to get all the descendants of.</param>
    /// <returns>The descendants in pre-order of the given symbol.</returns>
    public static IEnumerable<ISymbol> GetAllDescendantsAndSelf(this ISymbol symbol) {
      yield return symbol;
      foreach (var child in symbol.Children) {
        foreach (var descendant in GetAllDescendantsAndSelf(child)) {
          yield return descendant;
        }
      }
    }
    public static IEnumerable<TSymbol> AsEnumerable<TSymbol>(this TSymbol? symbol) where TSymbol : ISymbol {
      if (symbol != null) {
        yield return symbol;
      }
    }
  }
}
