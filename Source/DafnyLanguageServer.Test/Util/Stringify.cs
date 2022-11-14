#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util; 

public static class StringifyUtil {

  public static string Stringify(this object root, bool showNullChildren = false) {

    var builder = new StringBuilder();

    void Helper(ImmutableHashSet<object> visited, object? value, int indentation) {
      if (value == null) {
        builder.Append("null");
        return;
      }

      if (value is IEnumerable<object> enumerable) {
        var sep = "";
        builder.Append("[ ");
        var newIndentation = indentation + 2;
        foreach (var child in enumerable) {
          builder.AppendLine(sep);
          builder.Append(new String(' ', newIndentation));
          Helper(visited, child, newIndentation);
          sep = ", ";
        }

        if (sep != "") {
          builder.AppendLine();
          builder.Append(new String(' ', indentation));
        }
        builder.Append("]");

        return;
      }

      if (value is string) {
        builder.Append($"\"{value}\"");
        return;
      }

      var type = value.GetType();
      if (type.Namespace?.StartsWith("System") == true) {
        builder.Append(value);
        return;
      }

      var properties = type.GetProperties();
      if (properties.Any(p => p.PropertyType.IsAssignableTo(typeof(IEnumerable<object>)))) {

        if (visited.Contains(value)) {
          builder.Append("<visited>");
          return;
        }
        var newVisited = visited.Add(value);

        builder.Append(type.Name + " { ");
        var objectSep = "";
        foreach (var property in properties) {
          var child = property.GetValue(value);
          if (!showNullChildren && child == null) {
            continue;
          }
          builder.Append(objectSep);
          builder.Append(property.Name + ": ");
          Helper(newVisited, child, indentation);
          objectSep = ", ";
        }
        builder.Append(" }");
      } else {
        builder.Append(value);
      }
    }

    Helper(ImmutableHashSet.Create<object>(), root, 0);

    return builder.ToString()!;
  }
}