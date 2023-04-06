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

namespace Microsoft.Dafny; 

public class ProjectFile {
  [IgnoreDataMember]
  public Uri Uri { get; set; }
  public string[] Includes { get; set;  }
  public string[] Excludes { get; set;  }
  public Dictionary<string, object> Options { get; set;  }
  
  public static ProjectFile Open(Uri uri, TextWriter errorWriter) {
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

  public void ApplyToOptions(DafnyOptions options) {
    var matcher = new Matcher();
    foreach (var includeGlob in Includes)
    {
      matcher.AddInclude(includeGlob);
    }
    foreach (var includeGlob in Excludes) {
      matcher.AddExclude(includeGlob);
    }

    var root = Path.GetDirectoryName(Uri.LocalPath);
    var result = matcher.Execute(new DirectoryInfoWrapper(new DirectoryInfo(root!)));
    var files = result.Files.Select(f => Path.Combine(root, f.Path));
    foreach (var file in files)
    {
      options.AddFile(file);
    }
  }

  public bool TryGetValue(Option option, out object value) {
    var name = option.Name.StartsWith("--") ? option.Name.Substring(2) : option.Name;

    return Options.TryGetValue(name, out value);
  }
}