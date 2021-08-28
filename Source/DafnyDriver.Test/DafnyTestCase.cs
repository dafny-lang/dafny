using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using DafnyDriver.Test.XUnitExtensions;
using Xunit.Abstractions;

namespace DafnyDriver.Test {
  
  /**
   * Specialization of CLITestCase that mainly exists to support a much more
   * concise definition of ToString().
   */
  public class DafnyTestCase : CLITestCase {

    private static readonly Assembly dafnyDriverAssembly = Assembly.GetAssembly(typeof(Microsoft.Dafny.DafnyDriver));
    
    private static readonly Dictionary<string, object> defaultDafnyOptions = new() {
      ["countVerificationErrors"] = "0",

      // We do not want absolute or relative paths in error messages, just the basename of the file
      ["useBaseNameForFileName"] = "yes",

      // We do not want output such as "Compiled program written to Foo.cs"
      // from the compilers, since that changes with the target language
      ["compileVerbose"] = "0",
      
      // Hide Boogie execution traces since they are meaningless for Dafny programs
      ["errorTrace"] = "0"
    };

    private static IEnumerable<string> OptionsToFullArguments(string sourcePath,
      Dictionary<string, object> dafnyOptions, List<string> otherFiles) 
    {
      Dictionary<string, object> optionsWithDefaults = new(defaultDafnyOptions);
      foreach (var (key, value) in dafnyOptions) {
        optionsWithDefaults[key] = value;
      }

      return OptionsToArguments(sourcePath, optionsWithDefaults, otherFiles);
    }

    private static IEnumerable<string> OptionsToArguments(string sourcePath, Dictionary<string, object> dafnyOptions, List<string> otherFiles) {
      return new []{ sourcePath }
        .Concat(otherFiles)
        .Concat(dafnyOptions.Select(ConfigPairToArgument));
    }
    
    private static string ConfigPairToArgument(KeyValuePair<string, object> pair) {
      if (pair.Value.Equals("yes")) {
        return $"/{pair.Key}";
      }
      return $"/{pair.Key}:{pair.Value}";
    }

    private string BasePath;
    private string SourcePath;
    
    private Dictionary<string, object> DafnyOptions = new();
    private List<string> OtherFiles = new();

    public DafnyTestCase(string basePath, string fullSourcePath, Dictionary<string, object> dafnyOptions, List<string> otherFiles,
                         Expectation expected, bool invokeDirectly)
      : base(dafnyDriverAssembly, OptionsToFullArguments(fullSourcePath, dafnyOptions, otherFiles), new List<string>(), expected, invokeDirectly) {
      BasePath = basePath;
      SourcePath = fullSourcePath;
      DafnyOptions = dafnyOptions;
      OtherFiles = otherFiles;
    }
    
    public DafnyTestCase() {
      
    }
    
    public void Serialize(IXunitSerializationInfo info) {
      base.Serialize(info);
      info.AddValue(nameof(BasePath), BasePath);
      info.AddValue(nameof(SourcePath), SourcePath);
      info.AddValue(nameof(DafnyOptions), DafnyOptions);
      info.AddValue(nameof(OtherFiles), OtherFiles);
    }
    
    public void Deserialize(IXunitSerializationInfo info) {
      base.Deserialize(info);
      BasePath = info.GetValue<string>(nameof(BasePath));
      SourcePath = info.GetValue<string>(nameof(SourcePath));
      DafnyOptions = info.GetValue<Dictionary<string, object>>(nameof(DafnyOptions));
      OtherFiles = info.GetValue<List<string>>(nameof(OtherFiles));
    }
    
    public override string ToString() {
      var relativePath = SourcePath[(BasePath.Length + 1)..];
      return String.Join(" ", OptionsToArguments(relativePath, DafnyOptions, OtherFiles));
    }
  }
}