using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using Microsoft.Extensions.FileProviders;
using Microsoft.VisualBasic.CompilerServices;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using XUnitExtensions;
using YamlDotNet.Core;
using YamlDotNet.Serialization;
using YamlDotNet.Serialization.NamingConventions;
using YamlDotNet.Serialization.NodeDeserializers;
using YamlDotNet.Serialization.ObjectFactories;

namespace DafnyTests {
  
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
      if (obj is ForEachArgumentList forEach) {
        return forEach;
      } else {
        return new[] {(string)obj};
      }
    }

    private static IEnumerable<KeyValuePair<string, object>> ExpandValue(KeyValuePair<string, object> pair) {
      return Expand(pair.Value).Select(v => new KeyValuePair<string, object>(pair.Key, v));
    }
  }

  public class ForEachArgumentList : List<string> { }
  
  // TODO-RS: This is really close to a generic CLI test case -
  // can we move all the dafny-specific stuff to DafnyTestSpec instead?
  public class DafnyTestCase: IXunitSerializable {

    public string[] Arguments;

    public class Expectation : IXunitSerializable {
      // May be null if the test doesn't need to check the output
      public string OutputFile;
      public int ExitCode = 0;

      public string SpecialCaseReason;

      public static Expectation NO_OUTPUT = new Expectation(0, null, null);
      
      public Expectation(int exitCode, string outputFile, string specialCaseReason) {
        ExitCode = exitCode;
        OutputFile = outputFile;
        SpecialCaseReason = specialCaseReason;
      }

      public Expectation() {
        
      }
      
      public void Deserialize(IXunitSerializationInfo info) {
        OutputFile = info.GetValue<string>(nameof(OutputFile));
        ExitCode = info.GetValue<int>(nameof(ExitCode));
        SpecialCaseReason = info.GetValue<string>(nameof(SpecialCaseReason));
      }

      public void Serialize(IXunitSerializationInfo info) {
        info.AddValue(nameof(OutputFile), OutputFile);
        info.AddValue(nameof(ExitCode), ExitCode);
        info.AddValue(nameof(SpecialCaseReason), SpecialCaseReason);
      }

      public Expectation Adjust() {
        return new Expectation(ExitCode, OutputFile == null ? null : "comp/" + OutputFile, SpecialCaseReason);
      }
      
      public override string ToString() {
        string result;
        if (ExitCode != 0) {
          result = String.Format("<failure: {0}>", ExitCode);
        } else if (OutputFile != null) {
          result = OutputFile;
        } else {
          result = "<success>";
        }

        if (SpecialCaseReason != null) {
          result += " (special case)";
        }
        return result;
      }
    }

    public Expectation Expected;

    public DafnyTestCase(IEnumerable<string> arguments, Expectation expected) {
      Expected = expected;
      Arguments = arguments.ToArray();
    }

    public DafnyTestCase() {
      
    }
  
    public void Serialize(IXunitSerializationInfo info) {
      info.AddValue(nameof(Arguments), Arguments);
      info.AddValue(nameof(Expected), Expected);
    }
    
    public void Deserialize(IXunitSerializationInfo info) {
      Arguments = info.GetValue<string[]>(nameof(Arguments));
      Expected = info.GetValue<Expectation>(nameof(Expected));
    }

    public static ProcessResult RunDafny(IEnumerable<string> arguments) {
      // TODO-RS: Let these be overridden
      List<string> dafnyArguments = new List<string> {
        "/countVerificationErrors:0",

        // We do not want absolute or relative paths in error messages, just the basename of the file
        "/useBaseNameForFileName",

        // We do not want output such as "Compiled program written to Foo.cs"
        // from the compilers, since that changes with the target language
        "/compileVerbose:0"
      };
      dafnyArguments.AddRange(arguments);

      using (Process dafnyProcess = new Process()) {
        dafnyProcess.StartInfo.FileName = "dotnet";
        dafnyProcess.StartInfo.Arguments = "run --no-build --project ";
        dafnyProcess.StartInfo.Arguments += DafnyTestSpec.DAFNY_PROJ;
        dafnyProcess.StartInfo.Arguments += " --";
        foreach(var argument in dafnyArguments) {
          dafnyProcess.StartInfo.Arguments += " " + argument;
        }
        
        dafnyProcess.StartInfo.UseShellExecute = false;
        dafnyProcess.StartInfo.RedirectStandardOutput = true;
        dafnyProcess.StartInfo.RedirectStandardError = true;
        dafnyProcess.StartInfo.CreateNoWindow = true;
        // Necessary for JS to find bignumber.js
        dafnyProcess.StartInfo.WorkingDirectory = DafnyTestSpec.TEST_ROOT;

        // Only preserve specific whitelisted environment variables
        dafnyProcess.StartInfo.EnvironmentVariables.Clear();
        dafnyProcess.StartInfo.EnvironmentVariables.Add("PATH", Environment.GetEnvironmentVariable("PATH"));
        // Go requires this or GOCACHE
        dafnyProcess.StartInfo.EnvironmentVariables.Add("HOME", Environment.GetEnvironmentVariable("HOME"));

        dafnyProcess.Start();
        string output = dafnyProcess.StandardOutput.ReadToEnd();
        string error = dafnyProcess.StandardError.ReadToEnd();
        dafnyProcess.WaitForExit();
        return new ProcessResult(dafnyProcess.ExitCode, output, error);
      }
    }

    public void Run() {
      ProcessResult dafnyResult;
      if (Arguments.Any(arg => arg.StartsWith("/out"))) {
        dafnyResult = RunDafny(Arguments);
      } else {
        // Note that the temporary directory has to be an ancestor of Test
        // or else Javascript won't be able to locate bignumber.js :(
        using (var tempDir = new TemporaryDirectory(DafnyTestSpec.OUTPUT_DIR)) {
          // Add an extra component to the path to keep the files created inside the
          // temporary directory, since some compilers will
          // interpret the path as a single file basename rather than a directory.
          var outArgument = "/out:" + tempDir.DirInfo.FullName + "/Program";
          var dafnyArguments = new []{ outArgument }.Concat(Arguments);
          dafnyResult = RunDafny(dafnyArguments);
        }
      }

      if (dafnyResult.ExitCode != Expected.ExitCode) {
        throw new AssertActualExpectedException(Expected.ExitCode, dafnyResult.ExitCode,
          String.Format("Expected exit code to be {0} but was {1}. Standard error output:\n{2}",
            Expected.ExitCode, dafnyResult.ExitCode, dafnyResult.StandardError));
      }
      if (Expected.OutputFile != null) {
        var expectedOutput = File.ReadAllText(Path.Combine(DafnyTestSpec.TEST_ROOT, Expected.OutputFile));
        AssertWithDiff.Equal(expectedOutput, dafnyResult.StandardOutput);
      }

      Skip.If(Expected.SpecialCaseReason != null, Expected.SpecialCaseReason);
    }

    public override string ToString() {
      return String.Join(" ", Arguments) + " => " + Expected;
    }
  }

  
  public class DafnyTestYamlDataDiscoverer : YamlDataDiscoverer {

    private const string DEFAULT_CONFIG = 
@"!dafnyTestSpec
dafnyArguments: {}
";

    private static readonly IFileProvider ManifestFileProvider = new ManifestEmbeddedFileProvider(
      Assembly.GetExecutingAssembly());
    private static readonly Dictionary<string, string> PathsForResourceNames = GetPathsForResourceNames(
      "DafnyTests", ManifestFileProvider, "DafnyTests");
    
    private static Dictionary<string, string> GetPathsForResourceNames(string assemblyName, IFileProvider fileProvider, string path = null) {
      return fileProvider.GetDirectoryContents(path).SelectMany(file => {
        var childName = path == null ? file.Name : path + "/" + file.Name;
        if (file.IsDirectory) {
          return GetPathsForResourceNames(assemblyName, fileProvider, childName);
        } else {
          var result = new Dictionary<string, string>();
          result[ResourceNameForFilePath(assemblyName, childName)] = childName;
          return result;
        }
      }).ToDictionary(pair => pair.Key, pair => pair.Value);
    }

    private static string ResourceNameForFilePath(string assemblyName, string filePath) {
      return assemblyName + "." + filePath.Replace("/", ".").Replace("+", "_");
    }
    
    private static DafnyTestSpec SpecForResourceName(string manifestResourceName) {
      string filePath = PathsForResourceNames[manifestResourceName].Substring("DafnyTests/Test".Length + 1);
      return new DafnyTestSpec(filePath);
    }
    
    public static string GetTestCaseConfigYaml(string fullText) {
      var commentStart = fullText.IndexOf("/*");
      if (commentStart >= 0) {
        var commentEnd = fullText.IndexOf("*/", commentStart + 2);
        if (commentEnd >= 0) {
          var commentContent = fullText.Substring(commentStart + 2, commentEnd - commentStart - 2).Trim();
          if (commentContent.StartsWith("---")) {
            return commentContent;
          }
        }
      }

      return null;
    }
    
    public override IParser GetYamlParser(string manifestResourceName, Stream stream) {
      if (!manifestResourceName.EndsWith(".dfy")) {
        return null;
      }
      
      string content = GetTestCaseConfigYaml(new StreamReader(stream).ReadToEnd()) ?? DEFAULT_CONFIG;
  
      return new Parser(new StringReader(content));
    }

    public override IDeserializer GetDeserializer(string manifestResourceName) {
      var defaultObjectFactory = new DefaultObjectFactory();
      var customObjectFactory = new LambdaObjectFactory(type => 
        type == typeof(DafnyTestSpec) ? SpecForResourceName(manifestResourceName) : defaultObjectFactory.Create(type));
      
      return new DeserializerBuilder()
        .WithNamingConvention(CamelCaseNamingConvention.Instance)
        .WithTagMapping("!dafnyTestSpec", typeof(DafnyTestSpec))
        .WithTagMapping("!foreach", typeof(ForEachArgumentList))
        .WithObjectFactory(customObjectFactory)
        .Build();
    }
  }
  
  [DataDiscoverer("DafnyTests.DafnyTestYamlDataDiscoverer", "DafnyTests")]
  public class DafnyTestDataAttribute : YamlDataAttribute {
    public DafnyTestDataAttribute(bool withParameterNames) : base(withParameterNames) {
    }
  }
  
  public class DafnyTests {

    [Fact]
    public static void MetaTest() {
      var discoverer = new DafnyTestYamlDataDiscoverer();
      var testMethod = typeof(DafnyTests).GetMethod(nameof(Test));
      var testData = discoverer.GetData(testMethod, false).ToList();
      Assert.True(testData.Any());
    }

    [ParallelTheory]
    [DafnyTestData(false)]
    public static void Test(DafnyTestCase testCase) {
      testCase.Run();
    }
  }
}