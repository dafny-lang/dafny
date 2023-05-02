using System;
using System.Collections;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Reflection.Metadata;
using System.Runtime.Serialization;
using System.Text.Json;
using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis;
using Microsoft.Extensions.FileSystemGlobbing;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Tomlyn;
using Tomlyn.Model;

namespace Microsoft.Dafny; 

public class ProjectFile {
  public const string FileName = "dfyconfig.toml";

  [IgnoreDataMember]
  public Uri Uri { get; set; }
  public string[] Includes { get; set; }
  public string[] Excludes { get; set; }
  public Dictionary<string, object> Options { get; set; }

  public static ProjectFile Open(Uri uri, TextWriter errorWriter) {
    if (Path.GetFileName(uri.LocalPath) != FileName) {
      Console.WriteLine($"Warning: only Dafny project files named {FileName} are recognised by the Dafny IDE.");
    }
    try {
      var file = File.Open(uri.LocalPath, FileMode.Open);
      var model = Toml.ToModel<ProjectFile>(new StreamReader(file).ReadToEnd(), null, new TomlModelOptions());
      model.Uri = uri;
      return model;

    } catch (IOException e) {
      errorWriter.WriteLine(e.Message);
      return null;
    } catch (TomlException tomlException) {
      errorWriter.WriteLine($"The Dafny project file {uri.LocalPath} contains the following errors:");
      var regex = new Regex(
        @$"\((\d+),(\d+)\) : error : The property `(\w+)` was not found on object type {typeof(ProjectFile).FullName}");
      var newMessage = regex.Replace(tomlException.Message,
        match =>
          $"({match.Groups[1].Value},{match.Groups[2].Value}): the property {match.Groups[3].Value} does not exist.");
      errorWriter.WriteLine(newMessage);
      return null;
    }
  }

  public void AddFilesToOptions(DafnyOptions options) {
    var matcher = new Matcher();
    foreach (var includeGlob in Includes ?? new[] { "**/*.dfy" }) {
      matcher.AddInclude(includeGlob);
    }
    foreach (var includeGlob in Excludes ?? Enumerable.Empty<string>()) {
      matcher.AddExclude(includeGlob);
    }

    var root = Path.GetDirectoryName(Uri.LocalPath);
    var result = matcher.Execute(new DirectoryInfoWrapper(new DirectoryInfo(root!)));
    var files = result.Files.Select(f => Path.Combine(root, f.Path));
    foreach (var file in files) {
      options.AddFile(file);
    }
  }

  public void Validate(IEnumerable<Option> possibleOptions) {
    if (Options == null) {
      return;
    }

    var possibleNames = possibleOptions.Select(o => o.Name).ToHashSet();
    foreach (var optionThatDoesNotExist in Options.Where(option => !possibleNames.Contains(option.Key))) {
      Console.WriteLine(
        $"Warning: option '{optionThatDoesNotExist.Key}' that was specified in the project file, is not a valid Dafny option.");
    }
  }

  public bool TryGetValue(Option option, TextWriter errorWriter, out object value) {
    if (Options == null) {
      value = null;
      return false;
    }

    if (!Options.TryGetValue(option.Name, out value)) {
      return false;
    }

    if (option.ValueType.IsAssignableFrom(typeof(IList<string>)) && value is TomlArray valueArray) {
      value = valueArray.Select(e => (string)e).ToList();
    }

    if (!option.ValueType.IsInstanceOfType(value)) {
      errorWriter.WriteLine(
        $"Error: property '{option.Name}' is of type '{value.GetType()}' but should be of type '{option.ValueType}'");
      return false;
    }

    return true;

  }
}