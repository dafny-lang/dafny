using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Runtime.Serialization;
using System.Text.RegularExpressions;
using Microsoft.Extensions.FileSystemGlobbing;
using Tomlyn;
using Tomlyn.Model;

namespace Microsoft.Dafny; 

public class DafnyProject : IEquatable<DafnyProject> {
  public const string FileName = "dfyconfig.toml";

  public string ProjectName => Uri.ToString();

  public Uri UnsavedRootFile { get; set; }

  [IgnoreDataMember]
  public Uri Uri { get; set; }
  public string[] Includes { get; set; }
  public string[] Excludes { get; set; }
  public Dictionary<string, object> Options { get; set; }

  public static DafnyProject Open(IFileSystem fileSystem, Uri uri, TextWriter outputWriter, TextWriter errorWriter) {
    if (Path.GetFileName(uri.LocalPath) != FileName) {
      outputWriter.WriteLine($"Warning: only Dafny project files named {FileName} are recognised by the Dafny IDE.");
    }
    try {
      var model = Toml.ToModel<DafnyProject>(fileSystem.ReadFile(uri).ReadToEnd(), null, new TomlModelOptions());
      model.Uri = uri;
      return model;

    } catch (IOException e) {
      errorWriter.WriteLine(e.Message);
      return null;
    } catch (TomlException tomlException) {
      errorWriter.WriteLine($"The Dafny project file {uri.LocalPath} contains the following errors:");
      var regex = new Regex(
        @$"\((\d+),(\d+)\) : error : The property `(\w+)` was not found on object type {typeof(DafnyProject).FullName}");
      var newMessage = regex.Replace(tomlException.Message,
        match =>
          $"({match.Groups[1].Value},{match.Groups[2].Value}): the property {match.Groups[3].Value} does not exist.");
      errorWriter.WriteLine(newMessage);
      return null;
    }
  }

  public IEnumerable<Uri> GetRootSourceUris(IFileSystem fileSystem, DafnyOptions options) {
    if (!Uri.IsFile) {
      return Enumerable.Empty<Uri>();
    }

    var projectRoot = Path.GetDirectoryName(Uri.LocalPath)!;
    var matcher = new Matcher();
    foreach (var includeGlob in Includes ?? new[] { "**/*.dfy" }) {
      matcher.AddInclude(Path.GetFullPath(includeGlob, projectRoot));
    }
    foreach (var includeGlob in Excludes ?? Enumerable.Empty<string>()) {
      matcher.AddExclude(Path.GetFullPath(includeGlob, projectRoot));
    }

    var diskRoot = Path.GetPathRoot(Uri.LocalPath);
    var result = matcher.Execute(fileSystem.GetDirectoryInfoBase(diskRoot));
    var files = result.Files.Select(f => Path.Combine(diskRoot, f.Path));
    return files.Select(file => new Uri(Path.GetFullPath(file)));
  }

  public void Validate(TextWriter outputWriter, IEnumerable<Option> possibleOptions) {
    if (Options == null) {
      return;
    }

    var possibleNames = possibleOptions.Select(o => o.Name).ToHashSet();
    foreach (var optionThatDoesNotExist in Options.Where(option => !possibleNames.Contains(option.Key))) {
      outputWriter.WriteLine(
        $"Warning: option '{optionThatDoesNotExist.Key}' that was specified in the project file, is not a valid Dafny option.");
    }
  }

  public bool TryGetValue(Option option, TextWriter errorWriter, out object value) {
    if (Options == null) {
      value = null;
      return false;
    }

    if (!Options.TryGetValue(option.Name, out var tomlValue)) {
      value = null;
      return false;
    }

    return TryGetValueFromToml(errorWriter, Path.GetDirectoryName(Uri.LocalPath), option.Name, option.ValueType, tomlValue, out value);
  }

  public static bool TryGetValueFromToml(TextWriter errorWriter, string sourceDir, string tomlPath, System.Type type, object tomlValue, out object value) {
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

    if (type == typeof(FileInfo) && tomlValue is string tomlString) {
      // Need to make sure relative paths are interpreted relative to the source of the value,
      // not the current directory.
      var fullPath = sourceDir != null ? Path.GetFullPath(tomlString, sourceDir) : tomlString;
      value = new FileInfo(fullPath);
      return true;
    }

    if (!type.IsInstanceOfType(tomlValue)) {
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

  public bool Equals(DafnyProject other) {
    if (ReferenceEquals(null, other)) {
      return false;
    }

    if (ReferenceEquals(this, other)) {
      return true;
    }

    var orderedOptions = Options?.OrderBy(kv => kv.Key) ?? Enumerable.Empty<KeyValuePair<string, object>>();
    var otherOrderedOptions = other.Options?.OrderBy(kv => kv.Key) ?? Enumerable.Empty<KeyValuePair<string, object>>();
    
    return Equals(UnsavedRootFile, other.UnsavedRootFile) && Equals(Uri, other.Uri) &&
           // TODO set instead of sequence equality
           NullableSequenceEqual(Includes, other.Includes) &&
           NullableSequenceEqual(Excludes, other.Excludes) &&
           orderedOptions.SequenceEqual(otherOrderedOptions);
  }

  private static bool NullableSequenceEqual(IEnumerable<string> first, IEnumerable<string> second) {
    return first?.SequenceEqual(second) ?? (second == null);
  }

  public override bool Equals(object obj) {
    if (ReferenceEquals(null, obj)) {
      return false;
    }

    if (ReferenceEquals(this, obj)) {
      return true;
    }

    if (obj.GetType() != this.GetType()) {
      return false;
    }

    return Equals((DafnyProject)obj);
  }

  public override int GetHashCode() {
    return HashCode.Combine(UnsavedRootFile, Uri, Includes, Excludes, Options);
  }
}