using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Text;
using DiffPlex;
using DiffPlex.DiffBuilder;
using DiffPlex.DiffBuilder.Model;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using XUnitExtensions;
using YamlDotNet.RepresentationModel;
using YamlDotNet.Serialization;

namespace DafnyTests {

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

      public Expectation(string dafnyFile, Dictionary<string, string> config, string compileTarget) {
        config.TryGetValue("expect", out OutputFile);
        config.Remove("expect");
        if (OutputFile == null) {
          OutputFile = dafnyFile + ".expect";
          if (compileTarget != null) {
            var specialCasePath = dafnyFile + "." + compileTarget + ".expect";
            if (File.Exists(Path.Combine(TEST_ROOT, specialCasePath))) {
              SpecialCase = true;
              OutputFile = specialCasePath;
            }
          }
        } else if (OutputFile.Equals("no")) {
          OutputFile = null;
        }
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

    public DafnyTestCase(string dafnyFile, Dictionary<string, string> config, string compileTarget) {
      Expected = new Expectation(dafnyFile, config, compileTarget);
      
      DafnyFile = dafnyFile;
      Arguments = config.Select(ConfigPairToArgument).ToArray();
      
      var fullDafnyFilePath = Path.Combine(TEST_ROOT, DafnyFile);
      if (compileTarget != null) {
        Arguments = Arguments.Concat(new[] {"/compileTarget:" + compileTarget}).ToArray();
        // Include any additional files
        var additionalFilesPath = fullDafnyFilePath + "." + compileTarget + ".files";
        if (Directory.Exists(additionalFilesPath)) {
          var relativePaths = Directory.GetFiles(additionalFilesPath)
            .Select(path => Path.GetRelativePath(TEST_ROOT, path));
          Arguments = Arguments.Concat(relativePaths).ToArray();
        }
      }
    }

    public DafnyTestCase() {
      
    }

    public object[] ToMemberData() {
      string[] args = new[] {DafnyFile}.Concat(Arguments).ToArray();
      return new object[] {args, Expected};
    }
    
    public static string RunDafny(IEnumerable<string> arguments) {
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
        dafnyProcess.StartInfo.WorkingDirectory = TEST_ROOT;

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

    private static string GetTestCaseConfigString(string filePath) {
      // TODO-RS: Figure out how to do this cleanly on a TextReader instead,
      // and to handle things like nested comments.
      string fullText = File.ReadAllText(filePath);
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
    
    public static IEnumerable<object[]> TestCasesForDafnyFile(string filePath) {
      var fullFilePath = Path.Combine(TEST_ROOT, filePath);
      string configString = GetTestCaseConfigString(fullFilePath);
      IEnumerable<Dictionary<string, string>> configs;
      if (configString != null) {
        var yamlStream = new YamlStream();
        yamlStream.Load(new StringReader(configString));
        var config = yamlStream.Documents[0].RootNode;
        configs = YamlUtils.Expand(config).Select(ToDictionary);
      } else {
        configs = new[] { new Dictionary<string, string>() };
      }

      return configs.SelectMany(config => ResolveCompile(filePath, config))
                    .Select(t => t.ToMemberData());
    }

    private static Dictionary<string, string> ToDictionary(YamlNode node) {
      if (node is YamlMappingNode mapping) {
        return mapping.Children.ToDictionary(pair => pair.Key.ToString(), pair => pair.Value.ToString());
      } else {
        throw new ArgumentException("Bad test case configuration: " + node);
      }
    }
    
    private static IEnumerable<DafnyTestCase> ResolveCompile(string filePath, Dictionary<string, string> config) {
      var compile = "3";
      if (config.ContainsKey("compile")) {
        compile = config["compile"];
        config.Remove("compile");
      }
        
      if (compile.Equals("3") && !config.ContainsKey("compileTarget")) {
        var compileTargets = new[] {"cs", "java", "go", "js"};
        
        var justVerify = new Dictionary<string, string>(config);
        justVerify["compile"] = "0";
        justVerify["expect"] = "no";
        yield return new DafnyTestCase(filePath, justVerify, null);
        
        foreach (var compileTarget in compileTargets) {
          var withLanguage = new Dictionary<string, string>(config);
          withLanguage["noVerify"] = "yes";
          withLanguage["compile"] = "4";
          yield return new DafnyTestCase(filePath, withLanguage, compileTarget);
        }
      } else {
        config.TryGetValue("compileTarget", out var compileTarget);
        config["compile"] = compile;
        yield return new DafnyTestCase(filePath, config, compileTarget);
      }
    }

    private static string ConfigPairToArgument(KeyValuePair<string, string> pair) {
      if (pair.Key.Equals("otherFiles")) {
        return pair.Value.ToString();
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
        output = RunDafny(arguments);
      } else {
        // Note that the temporary directory has to be an ancestor of Test
        // or else Javascript won't be able to locate bignumber.js :(
        using (var tempDir = new TemporaryDirectory(OUTPUT_DIR)) {
          // Add an extra component to the path to keep the files created inside the
          // temporary directory, since some compilers will
          // interpret the path as a single file basename rather than a directory.
          var outArgument = "/out:" + tempDir.DirInfo.FullName + "/Program";
          var dafnyArguments = new []{ outArgument }.Concat(arguments);
          output = RunDafny(dafnyArguments);
        }
      }

      if (Expected.OutputFile != null) {
        var expectedOutput = File.ReadAllText(Path.Combine(TEST_ROOT, Expected.OutputFile));
        AssertWithDiff.Equal(expectedOutput, output);
      }

      Skip.If(Expected.SpecialCase, "Confirmed known exception for arguments: " + String.Join(" ", arguments));
    }
  }

  public class DafnyTests {
    
    public static IEnumerable<object[]> AllTestFiles() {
      var filePaths = Directory.GetFiles(DafnyTestCase.COMP_DIR, "*.dfy", SearchOption.AllDirectories)
                               .Select(path => Path.GetRelativePath(DafnyTestCase.TEST_ROOT, path));
      return filePaths.SelectMany(DafnyTestCase.TestCasesForDafnyFile);
    }

    [ParallelTheory]
    [MemberData(nameof(AllTestFiles))]
    public static void Test(string[] args, DafnyTestCase.Expectation expected) {
      var testCase = new DafnyTestCase();
      testCase.DafnyFile = args[0];
      testCase.Arguments = args.Skip(1).ToArray();
      testCase.Expected = expected;
      testCase.Run();
    }
  }
}