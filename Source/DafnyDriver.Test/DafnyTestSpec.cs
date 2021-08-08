using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using DafnyDriver.Test.XUnitExtensions;
using YamlDotNet.Serialization;
using YamlDotNet.Serialization.NamingConventions;
using YamlDotNet.Serialization.ObjectFactories;

namespace DafnyDriver.Test
{
  public class ForEachArgumentList : List<string> { }
  
  public class DafnyTestSpec: IEnumerable<DafnyTestCase> {

    private static readonly DirectoryInfo OUTPUT_ROOT = new(Directory.GetCurrentDirectory());
    
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
    
    public Dictionary<string, object> DafnyArguments = new();
    public List<string> OtherFiles = new();
    
    public Dictionary<string, DafnyTestSpec> CompileTargetOverrides = new();
    
    public CLITestCase.Expectation Expected;

    public DafnyTestSpec(string sourcePath) {
      SourcePath = sourcePath;
    }

    private DafnyTestSpec(string sourcePath, Dictionary<string, object> dafnyArguments, List<string> otherFiles, CLITestCase.Expectation expected) {
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
        yield return new DafnyTestSpec(SourcePath, justVerify, OtherFiles, CLITestCase.Expectation.NO_OUTPUT);
        
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
      foreach (var (key, value) in otherSpec.DafnyArguments) {
        mergedArguments[key] = value;
      }
      return new DafnyTestSpec(otherSpec.SourcePath, mergedArguments, OtherFiles.Concat(otherSpec.OtherFiles).ToList(), otherSpec.Expected);
    }
    
    private DafnyTestSpec ResolveExpected() {
      if (Expected == null) {
        return new DafnyTestSpec(SourcePath, DafnyArguments, OtherFiles, 
                                 new CLITestCase.Expectation(0, SourcePath + ".expect", null));
      }
      return this;
    }
    
    private DafnyTestCase ToTestCase() {
      return new DafnyTestCase(SourcePath, DafnyArguments, OtherFiles, Expected);
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