#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public static class StringifyUtil {

  public static void Stringify(this object root, TextWriter writer, bool showNullChildren = false) {

    void Helper(ImmutableHashSet<object> visited, object? value, int indentation) {
      if (value == null) {
        writer.Write("null");
        return;
      }

      if (value is IEnumerable<object> enumerable) {
        var sep = "";
        writer.Write("[ ");
        var newIndentation = indentation + 2;
        foreach (var child in enumerable) {
          writer.WriteLine(sep);
          writer.Write(new String(' ', newIndentation));
          Helper(visited, child, newIndentation);
          sep = ", ";
        }

        if (sep != "") {
          writer.WriteLine();
          writer.Write(new String(' ', indentation));
        }
        writer.Write("]");

        return;
      }

      if (value is string) {
        writer.Write($"\"{value}\"");
        return;
      }

      var type = value.GetType();
      if (type.Namespace?.StartsWith("System") == true) {
        writer.Write(value);
        return;
      }

      var properties = type.GetProperties();
      if (properties.Any(p => p.PropertyType.IsAssignableTo(typeof(IEnumerable<object>)))) {

        if (visited.Contains(value)) {
          writer.Write("<visited>");
          return;
        }
        var newVisited = visited.Add(value);

        writer.Write(type.Name + " { ");
        var objectSep = "";
        foreach (var property in properties) {
          var child = property.GetValue(value);
          if (!showNullChildren && child == null) {
            continue;
          }
          writer.Write(objectSep);
          writer.Write(property.Name + ": ");
          Helper(newVisited, child, indentation);
          objectSep = ", ";
        }
        writer.Write(" }");
      } else {
        writer.Write(value);
      }
    }

    Helper(ImmutableHashSet.Create<object>(), root, 0);
  }

  public static string Stringify(this object root, bool showNullChildren = false) {
    var stringWriter = new StringWriter();
    Stringify(root, stringWriter, showNullChildren);
    return stringWriter.ToString();
  }
}