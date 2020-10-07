using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
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
    public static readonly string OUTPUT_DIR = Path.Combine(TEST_ROOT, "Output") + Path.DirectorySeparatorChar;
    
    public static readonly string DAFNY_EXE = Path.Combine(DAFNY_ROOT, "Binaries/dafny");

    private static readonly IFileProvider manifestFileProvider = new ManifestEmbeddedFileProvider(
      Assembly.GetExecutingAssembly());
    private static readonly Dictionary<string, string> PathsForResourceNames = GetPathsForResourceNames(
      "DafnyTests", manifestFileProvider, "DafnyTests");
    
    public string SourcePath;
    public Dictionary<string, object> DafnyArguments = new Dictionary<string, object>();

    public DafnyTestCase.Expectation Expect = new DafnyTestCase.Expectation();

    public DafnyTestSpec(string manifestResourceName) {
      SourcePath = "comp/" + PathsForResourceNames[manifestResourceName].Substring("DafnyTests/Test".Length + 1);
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
      return ExpandArguments(DafnyArguments)
        .SelectMany(args => ResolveCompile(SourcePath, args, Expect))
        .GetEnumerator();
    }
    
    private static IEnumerable<DafnyTestCase> ResolveCompile(string sourcePath, Dictionary<string, string> config, DafnyTestCase.Expectation expect) {
      var compile = "3";
      if (config.ContainsKey("compile")) {
        compile = config["compile"];
        config.Remove("compile");
      }
        
      if (compile.Equals("3") && !config.ContainsKey("compileTarget")) {
        var compileTargets = new[] {"cs", "java", "go", "js"};
        
        var justVerify = new Dictionary<string, string>(config);
        justVerify["compile"] = "0";
        yield return new DafnyTestCase(sourcePath, justVerify, null, DafnyTestCase.Expectation.NO_OUTPUT);
        
        foreach (var compileTarget in compileTargets) {
          var withLanguage = new Dictionary<string, string>(config);
          withLanguage["noVerify"] = "yes";
          withLanguage["compile"] = "4";
          yield return new DafnyTestCase(sourcePath, withLanguage, compileTarget, expect.Resolve(sourcePath, compileTarget));
        }
      } else {
        config.TryGetValue("compileTarget", out var compileTarget);
        config["compile"] = compile;
        yield return new DafnyTestCase(sourcePath, config, compileTarget, expect.Resolve(sourcePath, compileTarget));
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }
    
    private static IEnumerable<Dictionary<string, string>> ExpandArguments(Dictionary<string, object> arguments) {
      return arguments.Select(ExpandValue)
                      .CartesianProduct()
                      .Select(e => e.ToDictionary(p => p.Key, p => p.Value));
    }
    
    public static IEnumerable<string> Expand(object obj) {
      if (obj is IEnumerable<string> e) {
        return e;
      } else {
        return new[] {(string)obj};
      }
    }

    private static IEnumerable<KeyValuePair<string, string>> ExpandValue(KeyValuePair<string, object> pair) {
      return Expand(pair.Value).Select(v => new KeyValuePair<string, string>(pair.Key, v));
    }
  }
  
  public class DafnyTestCase: IXunitSerializable {

    public string[] Arguments;

    public class Expectation : IXunitSerializable {
      // May be null if the test doesn't need to check the output
      public string OutputFile;
      public int ExitCode = 0;

      public bool SpecialCase = false;

      public static Expectation NO_OUTPUT = new Expectation(0, null);
      
      public Expectation Resolve(string sourceFile, string compileTarget) {
        Expectation result = (Expectation)MemberwiseClone();
        if (result.OutputFile == null) {
          result.OutputFile = sourceFile + ".expect";
          if (compileTarget != null) {
            var specialCasePath = sourceFile + "." + compileTarget + ".expect";
            if (File.Exists(DafnyTestSpec.TEST_ROOT + specialCasePath)) {
              result.SpecialCase = true;
              result.OutputFile = specialCasePath;
            }
          }
        } else if (result.OutputFile.Equals("no")) {
          result.OutputFile = null;
        }

        return result;
      }

      public Expectation(int exitCode, string outputFile) {
        ExitCode = exitCode;
        OutputFile = outputFile;
      }

      public Expectation() {
        
      }
      
      public void Deserialize(IXunitSerializationInfo info) {
        OutputFile = info.GetValue<string>(nameof(OutputFile));
        ExitCode = info.GetValue<int>(nameof(ExitCode));
        SpecialCase = info.GetValue<bool>(nameof(SpecialCase));
      }

      public void Serialize(IXunitSerializationInfo info) {
        info.AddValue(nameof(OutputFile), OutputFile);
        info.AddValue(nameof(ExitCode), ExitCode);
        info.AddValue(nameof(SpecialCase), SpecialCase);
      }

      public override string ToString() {
        return OutputFile ?? "-";
      }
    }

    public Expectation Expected;

    public DafnyTestCase(string dafnyFile, Dictionary<string, string> config, string compileTarget, Expectation expected) {
      Expected = expected;
      
      var arguments = new []{ dafnyFile }.Concat(config.Select(ConfigPairToArgument)).ToList();
      
      if (compileTarget != null) {
        arguments.Add("/compileTarget:" + compileTarget);
        // Include any additional files
        var additionalFilesPath = DafnyTestSpec.TEST_ROOT + dafnyFile + "." + compileTarget + ".files";
        if (Directory.Exists(additionalFilesPath)) {
          var relativePaths = Directory.GetFiles(additionalFilesPath)
            .Select(path => Path.GetRelativePath(DafnyTestSpec.TEST_ROOT, path));
          arguments.AddRange(relativePaths);
        }
      }
      
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

    public static string RunDafny(IEnumerable<string> arguments) {
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
        if (dafnyProcess.ExitCode != 0) {
          var message = String.Format("Non-zero Dafny exit code: {0}\n{1}\n{2}", dafnyProcess.ExitCode, output, error);
          Assert.True(false,  message);
        }

        return output + error;
      }
    }

    private static string ConfigPairToArgument(KeyValuePair<string, string> pair) {
      if (pair.Value.Equals("yes")) {
        return String.Format("/{0}", pair.Key);
      } else {
        return String.Format("/{0}:{1}", pair.Key, pair.Value);
      }
    }

    public void Run() {
      string output;
      if (Arguments.Any(arg => arg.StartsWith("/out"))) {
        output = RunDafny(Arguments);
      } else {
        // Note that the temporary directory has to be an ancestor of Test
        // or else Javascript won't be able to locate bignumber.js :(
        using (var tempDir = new TemporaryDirectory(DafnyTestSpec.OUTPUT_DIR)) {
          // Add an extra component to the path to keep the files created inside the
          // temporary directory, since some compilers will
          // interpret the path as a single file basename rather than a directory.
          var outArgument = "/out:" + tempDir.DirInfo.FullName + "/Program";
          var dafnyArguments = new []{ outArgument }.Concat(Arguments);
          output = RunDafny(dafnyArguments);
        }
      }

      if (Expected.OutputFile != null) {
        var expectedOutput = File.ReadAllText(Path.Combine(DafnyTestSpec.TEST_ROOT, Expected.OutputFile));
        AssertWithDiff.Equal(expectedOutput, output);
      }

      Skip.If(Expected.SpecialCase, "Confirmed known exception for arguments: " + String.Join(" ", Arguments));
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