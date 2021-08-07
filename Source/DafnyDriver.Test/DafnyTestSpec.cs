using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using YamlDotNet.Serialization;
using YamlDotNet.Serialization.NamingConventions;
using YamlDotNet.Serialization.ObjectFactories;

namespace DafnyDriver.Test
{
  public class ForEachArgumentList : List<string> { }
  
  public class DafnyTestSpec: IEnumerable<DafnyTestCase> {

    private static DirectoryInfo OUTPUT_ROOT = new DirectoryInfo(Directory.GetCurrentDirectory());
    
    // TODO-RS: This is an ugly method of locating the project root.
    // The proper fix is to run entirely out of the output directory,
    // and the projects are at least partially configured to make that possible,
    // but it's not quite working yet.
    private static string DAFNY_ROOT = 
      OUTPUT_ROOT.Parent.Parent.Parent.Parent.Parent.FullName;

    public static readonly string TEST_ROOT = Path.Combine(DAFNY_ROOT, "Test") + Path.DirectorySeparatorChar;
    public static readonly string OUTPUT_DIR = Path.Combine(TEST_ROOT, "Output") + Path.DirectorySeparatorChar;
    
    public static readonly string DAFNY_PROJ = Path.Combine(DAFNY_ROOT, "Source/DafnyDriver/DafnyDriver.csproj");

    // Dafny options with special handling
    public const string DAFNY_COMPILE_OPTION = "compile";
    public const string DAFNY_COMPILE_TARGET_OPTION = "compileTarget";
    public const string DAFNY_NO_VERIFY_OPTION = "noVerify";

    // Absolute file system path to the main Dafny file
    [YamlIgnore]
    public readonly string SourcePath;
    
    public Dictionary<string, object> DafnyArguments = new Dictionary<string, object>();
    public List<string> OtherFiles = new List<string>();
    
    public Dictionary<string, DafnyTestSpec> CompileTargetOverrides = new Dictionary<string, DafnyTestSpec>();
    
    public DafnyTestCase.Expectation Expected;

    public DafnyTestSpec(string sourcePath) {
      SourcePath = sourcePath;
    }

    private DafnyTestSpec(string sourcePath, Dictionary<string, object> dafnyArguments, List<string> otherFiles, DafnyTestCase.Expectation expected) {
      SourcePath = sourcePath;
      DafnyArguments = dafnyArguments;
      OtherFiles = otherFiles;
      Expected = expected;
    }
    
    public IEnumerator<DafnyTestCase> GetEnumerator() {
      return ResolveCompile()
        .SelectMany(spec => spec.ExpandArguments())
        .Select(spec => spec.ResolveExpected().ToTestCase())
        .GetEnumerator();
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    [YamlIgnore]
    public int? Compile {
      get {
        if (DafnyArguments.TryGetValue(DAFNY_COMPILE_OPTION, out var compile)) {
          return Int32.Parse((string) compile);
        }
        return null;
      }
      set {
        if (value != null) {
          DafnyArguments[DAFNY_COMPILE_OPTION] = value.ToString();
        } else {
          DafnyArguments.Remove(DAFNY_COMPILE_OPTION);
        }
      }
    }
    
    [YamlIgnore]
    public string CompileTarget {
      get {
        if (DafnyArguments.TryGetValue(DAFNY_COMPILE_TARGET_OPTION, out var compileTarget)) {
          return (string) compileTarget;
        }
        return null;
      }
    }

    private IEnumerable<DafnyTestSpec> ResolveCompile() {
      if (Compile == null) {
        Compile = 3;
      }
      
      if (Compile > 0 && CompileTarget == null) {
        // TODO: Include c++ but flag as special case by default?
        var compileTargets = new[] {"cs", "java", "go", "js"};

        var justVerify = new Dictionary<string, object>(DafnyArguments) {
          [DAFNY_COMPILE_OPTION] = "0"
        };
        yield return new DafnyTestSpec(SourcePath, justVerify, OtherFiles, DafnyTestCase.Expectation.NO_OUTPUT);
        
        foreach (var compileTarget in compileTargets) {
          var withLanguage = new Dictionary<string, object>(DafnyArguments) {
              [DAFNY_NO_VERIFY_OPTION] = "yes", 
              [DAFNY_COMPILE_OPTION] = Compile > 2 ? "4" : "2",
              [DAFNY_COMPILE_TARGET_OPTION] = compileTarget
            };
          var specForLanguage = new DafnyTestSpec(SourcePath, withLanguage, OtherFiles, Expected);
          if (CompileTargetOverrides.TryGetValue(compileTarget, out var compileTargetOverride)) {
            yield return specForLanguage.ApplyOverride(compileTargetOverride);
          } else {
            yield return specForLanguage;
          }
        }
      } else {
        yield return this;
      }
    }

    private DafnyTestSpec ApplyOverride(DafnyTestSpec otherSpec) {
      var mergedArguments = new Dictionary<string, object>(DafnyArguments);
      foreach (KeyValuePair<string, object> pair in otherSpec.DafnyArguments) {
        mergedArguments[pair.Key] = pair.Value;
      }
      return new DafnyTestSpec(otherSpec.SourcePath, mergedArguments, OtherFiles.Concat(otherSpec.OtherFiles).ToList(), otherSpec.Expected);
    }
    
    private DafnyTestSpec ResolveExpected() {
      if (Expected == null) {
        return new DafnyTestSpec(SourcePath, DafnyArguments, OtherFiles, 
                                 new DafnyTestCase.Expectation(0, SourcePath + ".expect", null));
      }
      return this;
    }
    
    private DafnyTestCase ToTestCase() {
      var arguments = new []{ SourcePath }
        .Concat(DafnyArguments.Select(ConfigPairToArgument));
      return new DafnyTestCase(arguments, Expected);
    }
    
    private static string ConfigPairToArgument(KeyValuePair<string, object> pair) {
      if (pair.Value.Equals("yes")) {
        return String.Format("/{0}", pair.Key);
      } else {
        return String.Format("/{0}:{1}", pair.Key, pair.Value);
      }
    }

    private IEnumerable<DafnyTestSpec> ExpandArguments() {
      return DafnyArguments.Select(ExpandValue)
                           .CartesianProduct()
                           .Select(e => e.ToDictionary(p => p.Key, p => p.Value))
                           .Select(args => new DafnyTestSpec(SourcePath, args, OtherFiles, Expected));
    }

    public static IEnumerable<string> Expand(object obj) {
      if (obj is ForEachArgumentList forEachArgumentList) {
        return forEachArgumentList;
      } else {
        return new[] {(string)obj};
      }
    }

    private static IEnumerable<KeyValuePair<string, object>> ExpandValue(KeyValuePair<string, object> pair) {
      return Expand(pair.Value).Select(v => new KeyValuePair<string, object>(pair.Key, v));
    }
  }
}