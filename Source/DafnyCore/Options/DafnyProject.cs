#nullable enable
using System;
using System.Collections;
using System.Collections.Generic;
using System.CommandLine;
using System.Diagnostics.CodeAnalysis;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore.Options;
using Microsoft.Extensions.FileSystemGlobbing;
using Tomlyn;
using Tomlyn.Model;

namespace Microsoft.Dafny;

public class DafnyProject : IEquatable<DafnyProject> {
  public static Option<bool> FindProjectOption = new("--find-project",
    "Uses the first specified input file as a starting path, from which to search for a project file by traversing up the file tree.");

  static DafnyProject() {
    OptionRegistry.RegisterOption(FindProjectOption, OptionScope.Cli);
  }

  public const string Extension = ".toml";
  public const string FileName = "dfyconfig" + Extension;

  public string ProjectName => Uri.ToString();

  public BatchErrorReporter Errors { get; init; } = new(DafnyOptions.Default);

  public int? Version { get; }
  public Uri Uri { get; set; }

  public Uri? Base { get; set; }

  public ISet<string> Includes { get; }
  public ISet<string> Excludes { get; }
  public IDictionary<string, object> Options { get; }

  public bool UsesProjectFile => Path.GetFileName(Uri.LocalPath).EndsWith(FileName);
  public bool ImplicitFromCli;

  public IOrigin StartingToken => ImplicitFromCli ? Token.Cli : new Token {
    Uri = Uri,
    line = 1,
    col = 1
  };

  public DafnyProject(int? version, Uri uri, Uri? @base, ISet<string> includes, ISet<string>? excludes = null, IDictionary<string, object>? options = null) {
    Version = version;
    Uri = uri;
    Base = @base;
    Includes = includes;
    Excludes = excludes ?? new HashSet<string>();
    Options = options ?? new Dictionary<string, object>();
  }

  public static async Task<DafnyProject> Open(IFileSystem fileSystem, Uri uri, IOrigin uriOrigin,
    bool defaultIncludes = true, bool serverNameCheck = true) {
    DafnyProject result;
    try {
      var fileSnapshot = fileSystem.ReadFile(uri);
      using var textReader = fileSnapshot.Reader;
      var text = await textReader.ReadToEndAsync();
      try {
        var model = Toml.ToModel<DafnyProjectFile>(text, null, new TomlModelOptions());
        var directory = Path.GetDirectoryName(uri.LocalPath)!;

        result = new DafnyProject(fileSnapshot.Version, uri, model.Base == null ? null : new Uri(Path.GetFullPath(model.Base, directory!)),
          model.Includes?.Select(p => Path.GetFullPath(p, directory)).ToHashSet() ?? [],
          model.Excludes?.Select(p => Path.GetFullPath(p, directory)).ToHashSet() ?? [],
          model.Options ?? new Dictionary<string, object>());

        if (result.Base != null) {
          var baseProject = await Open(fileSystem, result.Base, new Token {
            Uri = uri,
            line = 1,
            col = 1
          }, false, false);
          baseProject.Errors.CopyDiagnostics(result.Errors);
          foreach (var include in baseProject.Includes) {
            if (!result.Excludes.Contains(include)) {
              result.Includes.Add(include);
            }
          }

          foreach (var include in baseProject.Excludes) {
            if (!result.Includes.Contains(include)) {
              result.Excludes.Add(include);
            }
          }

          foreach (var option in baseProject.Options) {
            if (!result.Options.ContainsKey(option.Key)) {
              result.Options.Add(option.Key, option.Value);
            }
          }
        }
        if (defaultIncludes && model.Includes == null && !result.Includes.Any()) {
          result.Includes.Add("**/*.dfy");
        }
      } catch (TomlException tomlException) {
        var propertyNotFoundRegex = new Regex(
          @$"\((\d+),(\d+)\) : error : The property `(\w+)` was not found on object type {typeof(DafnyProject).FullName}");
        var propertyNotFoundMatch = propertyNotFoundRegex.Match(tomlException.Message);
        if (propertyNotFoundMatch.Success) {
          var line = int.Parse(propertyNotFoundMatch.Groups[1].Value);
          var column = int.Parse(propertyNotFoundMatch.Groups[2].Value);
          var property = propertyNotFoundMatch.Groups[3].Value;
          result = new DafnyProject(fileSnapshot.Version, uri, null, new HashSet<string>(), new HashSet<string>(),
            new Dictionary<string, object>());
          var token = new Token(line, column) {
            Uri = uri
          };
          result.Errors.Error(MessageSource.Project, token,
            $"Dafny project files do not have the property {property}");
        } else {
          var genericRegex = new Regex(@$"\((\d+),(\d+)\) : error : (.*)");
          var genericMatch = genericRegex.Match(tomlException.Message);
          if (genericMatch.Success) {
            var line = int.Parse(genericMatch.Groups[1].Value);
            var column = int.Parse(genericMatch.Groups[2].Value);
            var message = genericMatch.Groups[3].Value;
            result = new DafnyProject(fileSnapshot.Version, uri, null, new HashSet<string>(), new HashSet<string>(),
              new Dictionary<string, object>());
            var token = new Token(line, column) {
              Uri = uri
            };
            result.Errors.Error(MessageSource.Project, token, message);
          } else {
            throw new Exception("Could not parse Tomlyn error");
          }
        }
      }
    } catch (IOException e) {
      result = new DafnyProject(null, uri, null, new HashSet<string>(), new HashSet<string>(),
        new Dictionary<string, object>());
      result.Errors.Error(MessageSource.Project, uriOrigin, e.Message);
    }

    if (serverNameCheck && Path.GetFileName(uri.LocalPath) != FileName) {
      result.Errors.Warning(MessageSource.Project, "", result.StartingToken, $"only Dafny project files named {FileName} are recognised by the Dafny IDE.");
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
    return files.OrderBy(file => file).Select(file => new Uri(Path.GetFullPath(file))).
      Where(uri => !(uri.Equals(Uri) && uri.LocalPath.EndsWith(Extension)));
  }

  public bool ContainsSourceFile(Uri uri) {
    var matcher = GetMatcher(out var searchRoot);
    var fileSystemWithSourceFile = new InMemoryDirectoryInfoFromDotNet8(searchRoot, new[] { uri.LocalPath });
    return matcher.Execute(fileSystemWithSourceFile).HasMatches;
  }

  private Matcher GetMatcher(out string commonRoot) {
    var projectRoot = Path.GetDirectoryName(Uri.LocalPath)!;
    var diskRoot = Path.GetPathRoot(Uri.LocalPath)!;

    var includes = Includes;
    var excludes = Excludes;
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

  string? GetCommonParentDirectory(IReadOnlyList<string> strings) {
    if (!strings.Any()) {
      return null;
    }
    string commonPrefix = strings.FirstOrDefault() ?? "";

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
      commonPrefix = Path.GetDirectoryName(commonPrefix)!;
    }

    return commonPrefix;
  }

  public void Validate(TextWriter outputWriter, IEnumerable<Option> possibleOptions) {

    var possibleNames = possibleOptions.Select(o => o.Name).ToHashSet();
    foreach (var optionThatDoesNotExist in Options.Where(option => !possibleNames.Contains(option.Key))) {
      outputWriter.WriteLine(
        $"Warning: option '{optionThatDoesNotExist.Key}' that was specified in the project file, is not a valid Dafny option.");
    }
  }

  public bool TryGetValue(Option option, out object? value) {
    if (!Options.TryGetValue(option.Name, out var tomlValue)) {
      value = null;
      return false;
    }

    var printTomlValue = PrintTomlOptionToCliValue(Uri, tomlValue, option);
    var parseResult = option.Parse(printTomlValue.ToArray());
    if (parseResult.Errors.Any()) {
      Errors.Error(MessageSource.Project, StartingToken, $"could not parse value '{tomlValue}' for option '{option.Name}' that has type '{option.ValueType.Name}'");
      value = null;
      return false;
    }
    // By using the dynamic keyword, we can use the generic version of GetValueForOption which does type conversion,
    // which is sadly not accessible without generics.
    value = parseResult.GetValueForOption((dynamic)option);
    return true;
  }

  public static IEnumerable<string> PrintTomlOptionToCliValue(Uri uri, object value, Option valueType) {
    var projectDirectory = Path.GetDirectoryName(uri.LocalPath)!;

    if (value is TomlArray array) {
      List<string> elements;
      if (valueType.ValueType.IsAssignableTo(typeof(IEnumerable<FileInfo>))) {
        elements = array.Select(element => {
          if (element is string elementString) {
            return Path.GetFullPath(elementString, projectDirectory);
          }

          return element + "";
        }).ToList();
      } else {
        elements = array.Select(o => o + "").ToList();
      }

      return elements.SelectMany(e => new[] { valueType.Aliases.First(), e });
    }

    if (value is string stringValue && valueType.ValueType == typeof(FileInfo)) {
      value = Path.GetFullPath(stringValue, projectDirectory);
    }

    return new[] { valueType.Aliases.First(), value + "" };
  }

  public bool Equals(DafnyProject? other) {
    if (ReferenceEquals(null, other)) {
      return false;
    }

    if (ReferenceEquals(this, other)) {
      return true;
    }

    var orderedOptions = Options.OrderBy(kv => kv.Key);
    var otherOrderedOptions = other.Options.OrderBy(kv => kv.Key);

    return Equals(Uri, other.Uri) &&
           NullableSetEqual(Includes, other.Includes) &&
           NullableSetEqual(Excludes, other.Excludes) &&
           orderedOptions.SequenceEqual(otherOrderedOptions, new LambdaEqualityComparer<KeyValuePair<string, object>>(
             (kv1, kv2) => kv1.Key == kv2.Key && GenericEquals(kv1.Value, kv2.Value),
             kv => kv.GetHashCode()));
  }

  [SuppressMessage("ReSharper", "NotDisposedResource")]
  public static bool GenericEquals(object? first, object? second) {
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

  private static bool NullableSetEqual(ISet<string>? first, ICollection<string>? second) {
    if (first == null && second == null) {
      return true;
    }

    if (first == null || second == null) {
      return false;
    }
    return first.Count == second.Count && second.All(first.Contains);
  }

  public DafnyProject(DafnyProject original) {
    Uri = original.Uri;
    Includes = original.Includes.ToHashSet();
    Excludes = original.Excludes.ToHashSet();
    Options = original.Options.ToDictionary(kv => kv.Key, kv => kv.Value);
    Errors = original.Errors;
  }

  public DafnyProject Clone() {
    return new DafnyProject(this);
  }

  public override bool Equals(object? obj) {
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

  [SuppressMessage("ReSharper", "NonReadonlyMemberInGetHashCode")]
  public override int GetHashCode() {
    return HashCode.Combine(Uri, Includes, Excludes, Options);
  }
}

class DafnyProjectFile {
  public string? Base { get; set; }
  public string[]? Includes { get; set; }
  public string[]? Excludes { get; set; }
  public Dictionary<string, object>? Options { get; set; }
}