using System;
using System.Collections;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Parsing;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.Serialization;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore.Options;
using Microsoft.Extensions.FileSystemGlobbing;
using Tomlyn;
using Tomlyn.Model;

namespace Microsoft.Dafny; 

public class DafnyProject : IEquatable<DafnyProject> {
  public const string FileName = "dfyconfig.toml";

  public string ProjectName => Uri.ToString();

  [IgnoreDataMember]
  public BatchErrorReporter Errors { get; init; } = new(DafnyOptions.Default);

  [IgnoreDataMember]
  public Uri Uri { get; set; }
  public string[] Includes { get; set; }
  public string[] Excludes { get; set; }
  public Dictionary<string, object> Options { get; set; }
  public bool UsesProjectFile => Path.GetFileName(Uri.LocalPath) == FileName;

  public IToken StartingToken => new Token {
    Uri = Uri,
    line = 1,
    col = 1
  };

  public DafnyProject() {
  }

  public static async Task<DafnyProject> Open(IFileSystem fileSystem, Uri uri) {

    var emptyProject = new DafnyProject {
      Uri = uri
    };

    DafnyProject result;
    try {
      using var textReader = fileSystem.ReadFile(uri);
      var text = await textReader.ReadToEndAsync();
      var model = Toml.ToModel<DafnyProject>(text, null, new TomlModelOptions());
      model.Uri = uri;
      result = model;
    } catch (IOException e) {
      result = emptyProject;
      result.Errors.Error(MessageSource.Parser, result.StartingToken, e.Message);
    } catch (TomlException tomlException) {
      var regex = new Regex(
        @$"\((\d+),(\d+)\) : error : The property `(\w+)` was not found on object type {typeof(DafnyProject).FullName}");
      var newMessage = regex.Replace(tomlException.Message,
        match =>
          $"({match.Groups[1].Value},{match.Groups[2].Value}): the property {match.Groups[3].Value} does not exist.");
      result = emptyProject;
      result.Errors.Error(MessageSource.Parser, result.StartingToken, $"The Dafny project file {uri.LocalPath} contains the following errors: {newMessage}");
    }

    if (Path.GetFileName(uri.LocalPath) != FileName) {
      result.Errors.Warning(MessageSource.Parser, (string)null, result.StartingToken, $"only Dafny project files named {FileName} are recognised by the Dafny IDE.");
    }

    return result;
  }

  public IEnumerable<Uri> GetRootSourceUris(IFileSystem fileSystem) {
    if (!Uri.IsFile) {
      return new[] { Uri };
    }
    var matcher = GetMatcher(out var searchRoot);

    var result = matcher.Execute(fileSystem.GetDirectoryInfoBase(searchRoot));
    var files = result.Files.Select(f => Path.Combine(searchRoot, f.Path));
    return files.OrderBy(file => file).Select(file => new Uri(Path.GetFullPath(file)));
  }

  public bool ContainsSourceFile(Uri uri) {
    var matcher = GetMatcher(out var searchRoot);
    var fileSystemWithSourceFile = new InMemoryDirectoryInfoFromDotNet8(searchRoot, new[] { uri.LocalPath });
    return matcher.Execute(fileSystemWithSourceFile).HasMatches;
  }

  private Matcher GetMatcher(out string commonRoot) {
    var projectRoot = Path.GetDirectoryName(Uri.LocalPath)!;
    var diskRoot = Path.GetPathRoot(Uri.LocalPath)!;

    var includes = Includes ?? new[] { "**/*.dfy" };
    var excludes = Excludes ?? Array.Empty<string>();
    var fullPaths = includes.Concat(excludes).Select(p => Path.GetFullPath(p, projectRoot)).ToList();
    commonRoot = GetCommonParentDirectory(fullPaths) ?? diskRoot;
    var matcher = new Matcher();
    foreach (var includeGlob in includes) {
      matcher.AddInclude(Path.GetRelativePath(commonRoot, Path.GetFullPath(includeGlob, projectRoot)));
    }

    foreach (var excludeGlob in excludes) {
      matcher.AddExclude(Path.GetRelativePath(commonRoot, Path.GetFullPath(excludeGlob, projectRoot)));
    }

    return matcher;
  }

  string GetCommonParentDirectory(IReadOnlyList<string> strings) {
    if (!strings.Any()) {
      return null;
    }
    var commonPrefix = strings.FirstOrDefault() ?? "";

    foreach (var newString in strings) {
      var potentialMatchLength = Math.Min(newString.Length, commonPrefix.Length);

      if (potentialMatchLength < commonPrefix.Length) {
        commonPrefix = commonPrefix.Substring(0, potentialMatchLength);
      }

      for (var i = 0; i < potentialMatchLength; i++) {
        if (newString[i] == '*' || newString[i] != commonPrefix[i]) {
          commonPrefix = commonPrefix.Substring(0, i);
          break;
        }
      }
    }

    if (!Path.EndsInDirectorySeparator(commonPrefix)) {
      commonPrefix = Path.GetDirectoryName(commonPrefix);
    }

    return commonPrefix;
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

    var printTomlValue = PrintTomlOptionToCliValue(tomlValue, option);
    var parseResult = option.Parse(new[] { option.Aliases.First(), printTomlValue });
    if (parseResult.Errors.Any()) {
      errorWriter.WriteLine($"Error: Could not parse value '{tomlValue}' for option '{option.Name}' that has type '{option.ValueType.Name}'");
      value = null;
      return false;
    }
    // By using the dynamic keyword, we can use the generic version of GetValueForOption which does type conversion,
    // which is sadly not accessible without generics.
    value = parseResult.GetValueForOption((dynamic)option);
    return true;
  }

  string PrintTomlOptionToCliValue(object value, Option valueType) {
    var projectDirectory = Path.GetDirectoryName(Uri.LocalPath);

    if (value is TomlArray array) {
      if (valueType.ValueType.IsAssignableTo(typeof(IEnumerable<FileInfo>))) {
        return string.Join(" ", array.Select(element => {
          if (element is string elementString) {
            return Path.GetFullPath(elementString, projectDirectory!);
          }

          return element.ToString();
        }));
      }

      return string.Join(" ", array);
    }

    if (value is string stringValue && valueType.ValueType == typeof(FileInfo)) {
      value = Path.GetFullPath(stringValue, projectDirectory);
    }

    return value.ToString();
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

    return Equals(Uri, other.Uri) &&
           NullableSetEqual(Includes?.ToHashSet(), other.Includes) &&
           NullableSetEqual(Excludes?.ToHashSet(), other.Excludes) &&
           orderedOptions.SequenceEqual(otherOrderedOptions, new LambdaEqualityComparer<KeyValuePair<string, object>>(
             (kv1, kv2) => kv1.Key == kv2.Key && GenericEquals(kv1.Value, kv2.Value),
             kv => kv.GetHashCode()));
  }

  public static bool GenericEquals(object first, object second) {
    if (first == null && second == null) {
      return true;
    }

    if (first == null || second == null) {
      return false;
    }

    if (first is IEnumerable firstEnumerable && second is IEnumerable secondEnumerable) {
      var firstEnumerator = firstEnumerable.GetEnumerator();
      var secondEnumerator = secondEnumerable.GetEnumerator();

      while (true) {
        var a = firstEnumerator.MoveNext();
        var b = secondEnumerator.MoveNext();
        if (a != b) {
          return false;
        }

        if (!a) {
          return true;
        }

        if (!GenericEquals(firstEnumerator.Current, secondEnumerator.Current)) {
          return false;
        }
      }
    }

    return first.Equals(second);
  }

  private static bool NullableSetEqual(ISet<string> first, IReadOnlyCollection<string> second) {
    if (first == null && second == null) {
      return true;
    }

    if (first == null || second == null) {
      return false;
    }
    return first.Count == second.Count && second.All(first.Contains);
  }

  private static bool NullableSequenceEqual(IEnumerable<string> first, IEnumerable<string> second) {
    return first?.SequenceEqual(second) ?? (second == null);
  }

  public DafnyProject Clone() {
    return new DafnyProject() {
      Uri = Uri,
      Includes = Includes?.ToArray(),
      Excludes = Excludes?.ToArray(),
      Options = Options?.ToDictionary(kv => kv.Key, kv => kv.Value),
      Errors = Errors
    };
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
    return HashCode.Combine(Uri, Includes, Excludes, Options);
  }
}