using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Tomlyn.Model;

namespace DafnyCore.Generic; 

public static class TomlUtil {

  public static bool TryGetValueFromToml(TextWriter errorWriter, string sourceDir, string tomlPath, Type type, object tomlValue, out object value) {
    if (tomlValue == null) {
      value = null;
      return false;
    }

    if (type.IsAssignableFrom(typeof(List<string>))) {
      return TryGetListValueFromToml<string>(errorWriter, sourceDir, tomlPath, (TomlArray)tomlValue, out value);
    }
    if (type.IsAssignableFrom(typeof(List<FileInfo>))) {
      return TryGetListValueFromToml<FileInfo>(errorWriter, sourceDir, tomlPath, (TomlArray)tomlValue, out value);
    }

    if (tomlValue is string tomlString) {
      if (type == typeof(FileInfo)) {
        // Need to make sure relative paths are interpreted relative to the source of the value,
        // not the current directory.
        var fullPath = sourceDir != null ? Path.GetFullPath(tomlString, sourceDir) : tomlString;
        value = new FileInfo(fullPath);
        return true;
      }

      if (typeof(Enum).IsAssignableFrom(type)) {
        try {
          value = Enum.Parse(type, tomlString);
          return true;
        } catch (ArgumentException) {
          value = null;
          return false;
        }
      }
    }

    if (!type.IsInstanceOfType(tomlValue)) {
      if (type == typeof(string)) {
        value = tomlValue.ToString();
        return true;
      }
      errorWriter.WriteLine(
        $"Error: property '{tomlPath}' is of type '{tomlValue.GetType()}' but should be of type '{type}'");
      value = null;
      return false;
    }

    value = tomlValue;
    return true;
  }

  private static bool TryGetListValueFromToml<T>(TextWriter errorWriter, string sourceDir, string tomlPath, TomlArray tomlValue, out object value) {
    var success = true;
    value = tomlValue.Select((e, i) => {
      if (TryGetValueFromToml(errorWriter, sourceDir, $"{tomlPath}[{i}]", typeof(T), e, out var elementValue)) {
        return (T)elementValue;
      }
      success = false;
      return default(T);
    }).ToList();
    return success;
  }
}