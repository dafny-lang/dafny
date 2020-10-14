using Microsoft.Dafny;
using System.Collections.Generic;
using System.Text;

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
  }
}
