using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using XUnitExtensions;
using YamlDotNet.Core;
using YamlDotNet.RepresentationModel;
using YamlDotNet.Serialization;
using YamlDotNet.Serialization.NamingConventions;
using YamlDotNet.Serialization.ObjectFactories;

namespace DafnyTests {


  public class DafnyTestSpec : IEnumerable<DafnyTestCase> {

    public string SourcePath;
    public Dictionary<string, object> DafnyArguments = new Dictionary<string, object>();

    public DafnyTestCase.Expectation Expect = new DafnyTestCase.Expectation();

    public DafnyTestSpec(string manifestResourceName) {
      SourcePath = manifestResourceName;
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
  
  public class DafnyTestCase {

    private static DirectoryInfo OUTPUT_ROOT = new DirectoryInfo(Directory.GetCurrentDirectory());
    
    // TODO-RS: This is an ugly method of locating the project root.
    // The proper fix is to run entirely out of the output directory,
    // and the projects are at least partially configured to make that possible,
    // but it's not quite working yet.
    private static string DAFNY_ROOT =
      OUTPUT_ROOT.Parent.Parent.Parent.Parent.Parent.FullName;

    public static readonly string TEST_ROOT = Path.Combine(DAFNY_ROOT, "Test") + Path.DirectorySeparatorChar;
    public static string COMP_DIR = Path.Combine(TEST_ROOT, "comp") + Path.DirectorySeparatorChar;
    private static string OUTPUT_DIR = Path.Combine(TEST_ROOT, "Output") + Path.DirectorySeparatorChar;
    
    private static string DAFNY_EXE = Path.Combine(DAFNY_ROOT, "Binaries/dafny");
        
    public string DafnyFile;
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
            if (File.Exists(Path.Combine(TEST_ROOT, specialCasePath))) {
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
      
      DafnyFile = dafnyFile;
      Arguments = config.Select(ConfigPairToArgument).ToArray();
      
      if (compileTarget != null) {
        Arguments = Arguments.Concat(new[] {"/compileTarget:" + compileTarget}).ToArray();
        // Include any additional files
        var additionalFilesPath = dafnyFile + "." + compileTarget + ".files";
        IEnumerable<string> additionalFiles = GetType().Assembly.GetManifestResourceNames()
          .Where(name => name.StartsWith(additionalFilesPath));
        Arguments = Arguments.Concat(additionalFiles).ToArray();
      }
    }

    public DafnyTestCase() {
      
    }

    public static string RunDafny(string workingDirectory, IEnumerable<string> arguments) {
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
//        dafnyProcess.StartInfo.FileName = "mono";
        dafnyProcess.StartInfo.FileName = DAFNY_EXE;
        foreach (var argument in dafnyArguments) {
          dafnyProcess.StartInfo.Arguments += " " + argument;
        }

        dafnyProcess.StartInfo.UseShellExecute = false;
        dafnyProcess.StartInfo.RedirectStandardOutput = true;
        dafnyProcess.StartInfo.RedirectStandardError = true;
        dafnyProcess.StartInfo.CreateNoWindow = true;
        // Necessary for JS to find bignumber.js
//        dafnyProcess.StartInfo.WorkingDirectory = TEST_ROOT;
        dafnyProcess.StartInfo.WorkingDirectory = workingDirectory;

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
      if (pair.Key.Equals("otherFiles")) {
        return pair.Value;
      } else if (pair.Value.Equals("yes")) {
        return String.Format("/{0}", pair.Key);
      } else {
        return String.Format("/{0}:{1}", pair.Key, pair.Value);
      }
    }

    public void Run() {
      var arguments = new []{ DafnyFile }.Concat(Arguments);
      
      string output;
      if (arguments.Any(arg => arg.StartsWith("/out"))) {
        output = RunDafny(TEST_ROOT, arguments);
      } else {
        // Note that the temporary directory has to be an ancestor of Test
        // or else Javascript won't be able to locate bignumber.js :(
        using (var tempDir = new TemporaryDirectory(OUTPUT_DIR)) {
          using (var fileStream = File.Create(tempDir.DirInfo.FullName + "/" + DafnyFile)) {
            GetType().Assembly.GetManifestResourceStream(DafnyFile).CopyTo(fileStream);
          }
          
          // Add an extra component to the path to keep the files created inside the
          // temporary directory, since some compilers will
          // interpret the path as a single file basename rather than a directory.
          var outArgument = "/out:" + tempDir.DirInfo.FullName + "/Program";
          var dafnyArguments = new []{ outArgument }.Concat(arguments);
          output = RunDafny(tempDir.DirInfo.FullName, dafnyArguments);
        }
      }

      if (Expected.OutputFile != null) {
        var expectedOutput = new StreamReader(GetType().Assembly.GetManifestResourceStream(Expected.OutputFile)).ReadToEnd();
        AssertWithDiff.Equal(expectedOutput, output);
      }

      Skip.If(Expected.SpecialCase, "Confirmed known exception for arguments: " + String.Join(" ", arguments));
    }
  }

  
  public class DafnyTestYamlDataDiscoverer : YamlDataDiscoverer {

    private const string DEFAULT_CONFIG = @"
!dafnyTestSpec
dafnyArguments:
  compile: 3
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
      var customObjectFactory = new LambdaObjectFactory(type => {
        if (type == typeof(DafnyTestSpec)) {
          return new DafnyTestSpec(manifestResourceName);
        } else {
          return defaultObjectFactory.Create(type);
        }
      });
      
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
      var dataAttribute = testMethod.GetCustomAttributesData().ToList()[1];
      IEnumerable<object[]> data = discoverer.GetData(Reflector.Wrap(dataAttribute), Reflector.Wrap(testMethod));
      List<object[]> list = data.ToList();
    }
    
    [ParallelTheory]
    [DafnyTestData(false)]
    public static void Test(DafnyTestCase testCase) {
      testCase.Run();
    }
  }
}