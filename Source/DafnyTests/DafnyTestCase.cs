using System;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel.Design;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using FluentAssertions;
using Microsoft.Extensions.FileProviders;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using XUnitExtensions;
using YamlDotNet.Core;
using YamlDotNet.Serialization;
using YamlDotNet.Serialization.NamingConventions;
using YamlDotNet.Serialization.ObjectFactories;

namespace DafnyTests {
  
  public class DafnyTestSpec : IEnumerable<DafnyTestCase> {

    private static DirectoryInfo OUTPUT_ROOT = new DirectoryInfo(Directory.GetCurrentDirectory());
    
    // TODO-RS: This is an ugly method of locating the project root.
    // The proper fix is to run entirely out of the output directory,
    // and the projects are at least partially configured to make that possible,
    // but it's not quite working yet.
    private static string DAFNY_ROOT = 
      OUTPUT_ROOT.Parent.Parent.Parent.Parent.Parent.FullName;

    public static readonly string TEST_ROOT = Path.Combine(DAFNY_ROOT, "Test") + Path.DirectorySeparatorChar;
    public static readonly string COMP_DIR = Path.Combine(TEST_ROOT, "comp") + Path.DirectorySeparatorChar;
    public static readonly string OUTPUT_DIR = Path.Combine(TEST_ROOT, "Output") + Path.DirectorySeparatorChar;
    
    public static readonly string DAFNY_EXE = Path.Combine(DAFNY_ROOT, "Binaries/dafny");

    private static readonly IFileProvider manifestFileProvider = new ManifestEmbeddedFileProvider(
      Assembly.GetExecutingAssembly());
    private static readonly Dictionary<string, string> PathsForResourceNames = GetPathsForResourceNames(
      "DafnyTests", manifestFileProvider, "DafnyTests");
    
    // Absolute file system path to the main Dafny file
    public string SourcePath;
    
    public Dictionary<string, object> DafnyArguments = new Dictionary<string, object>();
    public IEnumerable<string> OtherFiles = Enumerable.Empty<string>();
    
    public Dictionary<string, DafnyTestSpec> CompileTargetOverrides = new Dictionary<string, DafnyTestSpec>();
    
    public DafnyTestCase.Expectation Expected;

    public DafnyTestSpec(string manifestResourceName) {
      SourcePath = COMP_DIR + PathsForResourceNames[manifestResourceName].Substring("DafnyTests/Test".Length + 1);
    }

    private DafnyTestSpec(string sourcePath, Dictionary<string, object> dafnyArguments, IEnumerable<string> otherFiles, DafnyTestCase.Expectation expected) {
      SourcePath = sourcePath;
      DafnyArguments = dafnyArguments;
      OtherFiles = otherFiles;
      Expected = expected;
    }
    
    private static Dictionary<string, string> GetPathsForResourceNames(string assemblyName, IFileProvider fileProvider, string path = null) {
      return fileProvider.GetDirectoryContents(path).SelectMany(file => {
        var childName = path == null ? file.Name : path + "/" + file.Name;
       if (file.IsDirectory) {
          return GetPathsForResourceNames(assemblyName, fileProvider, childName);
        } else {
          var result = new Dictionary<string, string>();
          result[assemblyName + "." + childName.Replace("/", ".")] = childName;
          return result;
        }
      }).ToDictionary(pair => pair.Key, pair => pair.Value);
    }
    
    public IEnumerator<DafnyTestCase> GetEnumerator() {
      return ResolveCompile()
        .SelectMany(spec => spec.ExpandArguments())
        .Select(spec => spec.ResolveExpected().ToTestCase())
        .GetEnumerator();
    }

    public string Compile {
      get {
        if (DafnyArguments.TryGetValue("compile", out var compile)) {
          return (string) compile;
        }
        return null;
      }
      set {
        DafnyArguments["compile"] = value;
      }
    }
    public string CompileTarget {
      get {
        if (DafnyArguments.TryGetValue("compileTarget", out var compileTarget)) {
          return (string) compileTarget;
        }
        return null;
      }
    }

    private IEnumerable<DafnyTestSpec> ResolveCompile() {
      if (Compile == null) {
        Compile = "3";
      }
      
      if ("3".Equals(Compile) && CompileTarget == null) {
        var compileTargets = new[] {"cs", "java", "go", "js"};

        var justVerify = new Dictionary<string, object>(DafnyArguments) {
          ["compile"] = "0"
        };
        yield return new DafnyTestSpec(SourcePath, justVerify, OtherFiles, DafnyTestCase.Expectation.NO_OUTPUT);
        
        foreach (var compileTarget in compileTargets) {
          var withLanguage = new Dictionary<string, object>(DafnyArguments) {
              ["noVerify"] = "yes", 
              ["compile"] = "4",
              ["compileTarget"] = compileTarget
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
      return new DafnyTestSpec(otherSpec.SourcePath, mergedArguments, OtherFiles.Concat(otherSpec.OtherFiles), otherSpec.Expected);
    }
    
    private DafnyTestSpec ResolveExpected() {
      if (Expected == null) {
        return new DafnyTestSpec(SourcePath, DafnyArguments, OtherFiles, 
                                 new DafnyTestCase.Expectation(0, Path.GetFileName(SourcePath) + ".expect", null));
      } else {
        return this;
      }
    }
    
    private DafnyTestCase ToTestCase() {
      var arguments = new []{ Path.GetRelativePath(TEST_ROOT, SourcePath) }
        .Concat(DafnyArguments.Select(ConfigPairToArgument))
        .Concat(OtherFiles.Select(otherFile => "comp/" + otherFile));
      return new DafnyTestCase(arguments, Expected.Adjust());
    }
    
    private static string ConfigPairToArgument(KeyValuePair<string, object> pair) {
      if (pair.Value.Equals("yes")) {
        return String.Format("/{0}", pair.Key);
      } else {
        return String.Format("/{0}:{1}", pair.Key, pair.Value);
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
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
        return OutputFile ?? "-";
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
        // Expected output does not contain logo
        "/nologo",
        "/countVerificationErrors:0",

        // We do not want absolute or relative paths in error messages, just the basename of the file
        "/useBaseNameForFileName",

        // We do not want output such as "Compiled program written to Foo.cs"
        // from the compilers, since that changes with the target language
        "/compileVerbose:0"
      };
      dafnyArguments.AddRange(arguments);

      using (Process dafnyProcess = new Process()) {
        dafnyProcess.StartInfo.FileName = DafnyTestSpec.DAFNY_EXE;
        foreach (var argument in dafnyArguments) {
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
        dafnyProcess.WaitForExit();
        string output = dafnyProcess.StandardOutput.ReadToEnd();
        string error = dafnyProcess.StandardError.ReadToEnd();
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
    
    public override IParser GetYamlParser(string manifestResourceName, Stream stream) {
      if (!manifestResourceName.EndsWith(".dfy")) {
        return null;
      }
      
      string content = DEFAULT_CONFIG;
      
      // TODO-RS: Figure out how to do this cleanly on a TextReader instead,
      // and to handle things like nested comments.
      string fullText = new StreamReader(stream).ReadToEnd();
      var commentStart = fullText.IndexOf("/*");
      if (commentStart >= 0) {
        var commentEnd = fullText.IndexOf("*/", commentStart + 2);
        if (commentEnd >= 0) {
          var commentContent = fullText.Substring(commentStart + 2, commentEnd - commentStart - 2).Trim();
          if (commentContent.StartsWith("---")) {
            content = commentContent;
          }
        }
      }
  
      return new Parser(new StringReader(content));
    }

    public override IDeserializer GetDeserializer(string manifestResourceName) {
      var defaultObjectFactory = new DefaultObjectFactory();
      var customObjectFactory = new LambdaObjectFactory(type => 
        type == typeof(DafnyTestSpec) ? new DafnyTestSpec(manifestResourceName) : defaultObjectFactory.Create(type));
      
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
    public DafnyTestDataAttribute(bool withParameterNames = true) : base(withParameterNames) {
    }
  }
  
  public class DafnyTests {

    [Fact]
    public static void MetaTest() {
      var discoverer = new DafnyTestYamlDataDiscoverer();
      var testMethod = typeof(DafnyTests).GetMethod(nameof(Test));
      discoverer.GetData(testMethod, false).ToList();
    }

    [ParallelTheory]
    [DafnyTestData(false)]
    public static void Test(DafnyTestCase testCase) {
      testCase.Run();
    }
  }
}