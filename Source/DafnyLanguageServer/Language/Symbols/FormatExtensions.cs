using System;
using System.Collections.Generic;
using System.Text;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Extension methods to format dafny and boogie symbols.
  /// </summary>
  public static class FormatExtensions {
    /// <summary>
    /// Converts the given enumerable of variables into a comma seperated string.
    /// </summary>
    /// <param name="variables">The variables to get the string representation of.</param>
    /// <returns>The string representation of the variables seperated by commas.</returns>
    public static string AsCommaSeperatedText<TVariable>(this IEnumerable<TVariable> variables) where TVariable : IVariable {
      var combined = new StringBuilder();
      foreach (var formal in variables) {
        if (combined.Length > 0) {
          combined.Append(", ");
        }
        combined.Append(formal.AsText());
      }
      return combined.ToString();
    }

    /// <summary>
    /// Returns a text representation of the given variable.
    /// </summary>
    /// <param name="variable">The variable to get a text representation of.</param>
    /// <returns>The text representation of the variable.</returns>
    public static string AsText(this IVariable variable) {
      var ghost = variable.IsGhost ? "ghost " : "";
      string type;
      try {
        type = variable.Type.ToString();
      } catch (Exception e) {
        type = $"<Internal error: {e.Message}>";
      }
      return $"{ghost}{variable.Name}: {type}";
    }

    /// <summary>
    /// Returns a text representation of the given formal.
    /// </summary>
    /// <param name="type">The type to get a text representation of.</param>
    /// <returns>The text representation of the type.</returns>
    public static string AsText(this Type type, DafnyOptions options) {
      // TODO Currently a copy of "ToString()".
      // TODO Use the module definition for the name resolution?
      return type.TypeName(options, null, false);
    }
  }
}
