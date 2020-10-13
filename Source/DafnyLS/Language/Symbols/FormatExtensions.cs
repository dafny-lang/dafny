using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Extension methods to format dafny and boogie symbols.
  /// </summary>
  internal static class FormatExtensions {
    /// <summary>
    /// Converts the given list of formals into a comma seperated string.
    /// </summary>
    /// <param name="formals">The formals to get the string representation of.</param>
    /// <returns>The string representation of the formals seperated by commas.</returns>
    public static string AsCommaSeperatedText(this IReadOnlyList<Formal> formals) {
      var combined = new StringBuilder();
      foreach(var formal in formals) {
        if(combined.Length > 0) {
          combined.Append(", ");
        }
        combined.Append(formal.AsText());
      }
      return combined.ToString();
    }

    /// <summary>
    /// Returns a text representation of the given formal.
    /// </summary>
    /// <param name="formal">The formal to get a text representation of.</param>
    /// <returns>The text representation of the formal.</returns>
    public static string AsText(this Formal formal) {
      return $"{formal.Name}:{formal.Type}";
    }


    /// <summary>
    /// Returns a text representation of the given formal.
    /// </summary>
    /// <param name="type">The type to get a text representation of.</param>
    /// <returns>The text representation of the type.</returns>
    public static string AsText(this Type type) {
      // TODO Currently a copy of "ToString()".
      // TODO Use the module definition for the name resolution?
      return type.TypeName(null, false);
    }

    /// <summary>
    /// Converts the specified enumerable of symbols into their LSP representation.
    /// </summary>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>An enumerable with the converted symbols in the LSP format.</returns>
    public static IEnumerable<DocumentSymbol> AsLspSymbols(this IEnumerable<ILocalizableSymbol> symbols, CancellationToken cancellationToken) {
      return symbols.WithCancellation(cancellationToken).Select(symbol => symbol.AsLspSymbol(cancellationToken));
    }
  }
}
