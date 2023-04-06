using System;
using System.Collections;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Runtime.Serialization;
using System.Text.Json;
using Microsoft.CodeAnalysis;
using Microsoft.Extensions.FileSystemGlobbing;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Tomlyn;

namespace Microsoft.Dafny; 

/// <summary>
/// {
///   options: {
///     warn-shadowing: true
///   }
/// }
/// </summary>
public class ProjectFile {
  [IgnoreDataMember]
  public Uri Uri { get; set; }
  public string[] Includes { get; set;  }
  public Dictionary<string, object> Options { get; set;  }
  
  public static ProjectFile Open(Uri uri) {
    var file = File.Open(uri.LocalPath, FileMode.Open);
    var model = Toml.ToModel<ProjectFile>(new StreamReader(file).ReadToEnd());
    model.Uri = uri;
    return model;
  }

  public void ApplyToOptions(Command command, DafnyOptions options) {
    ProcessIncludes(options);
  }

  private void ProcessIncludes(DafnyOptions options)
  {
    var matcher = new Matcher();
    foreach (var includeGlob in Includes)
    {
      matcher.AddInclude(includeGlob);
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