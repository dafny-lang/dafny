#nullable enable
using System;
using System.Collections;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

using Overrides = ImmutableDictionary<System.Type, Action<object, TextWriter>>;
public static class StringifyUtil {

  public static Overrides EmptyOverrides() {
    return ImmutableDictionary<System.Type, Action<object, TextWriter>>.Empty;
  }

  public static Overrides UseToString(this Overrides overrides, System.Type type) {
    return overrides.Add(type, (value, writer) => writer.Write(value.ToString()));
  }

  public static void Stringify(this object root, TextWriter writer, bool showNullChildren = false,
    IReadOnlyDictionary<System.Type, Action<object, TextWriter>>? overrides = null) {

    overrides = ImmutableDictionary<System.Type, Action<object, TextWriter>>.Empty;

    void Helper(ImmutableHashSet<object> visited, object? value, int indentation) {
      if (value == null) {
        writer.Write("null");
        return;
      }

      if (value is string) {
        writer.Write($"\"{value}\"");
        return;
      }

      var newIndentation = indentation + 2;
      if (value is IEnumerable enumerable) {
        var sep = "";
        writer.Write("[");
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

      var type = value.GetType();
      var isKeyValuePair = type.Name == "KeyValuePair`2";
      if (type.Namespace?.StartsWith("System") == true && !isKeyValuePair) {
        writer.Write(value);
        return;
      }

      if (value is Enum) {
        writer.Write(value.ToString());
        return;
      }

      if (visited.Contains(value)) {
        writer.Write("<visited>");
        return;
      }

      var overrideForType = overrides.GetValueOrDefault(type);
      if (overrideForType != null) {
        overrideForType(value, writer);
        return;
      }

      var newVisited = visited.Add(value);

      writer.Write((isKeyValuePair ? "" : (type.Name + " ")) + "{");
      var objectSep = "";
      var properties = type.GetProperties();
      foreach (var property in properties) {
        var child = property.GetValue(value);
        if (!showNullChildren && child == null) {
          continue;
        }

        writer.WriteLine(objectSep);
        writer.Write(new String(' ', newIndentation));
        writer.Write(property.Name + " = ");
        Helper(newVisited, child, newIndentation);
        objectSep = ",";
      }

      writer.WriteLine();
      writer.Write(new String(' ', indentation) + "}");
    }

    Helper(ImmutableHashSet.Create<object>(), root, 0);
    writer.Flush();
  }

  public static string Stringify(this object root, bool showNullChildren = false) {
    var stringWriter = new StringWriter();
    Stringify(root, stringWriter, showNullChildren);
    return stringWriter.ToString();
  }
}