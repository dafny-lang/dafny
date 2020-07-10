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

  public class DafnyTestCase : IXunitSerializable {

    private static DirectoryInfo OUTPUT_ROOT = new DirectoryInfo(Directory.GetCurrentDirectory());
    private static bool IS_NET_CORE => RuntimeInformation.FrameworkDescription.StartsWith(".NET Core", StringComparison.OrdinalIgnoreCase);
    // TODO-RS: This is an ugly method of locating the project root - .NET Core happens to
    // have the current directly one level deeper. The proper fix is to run entirely out of
    // the output directory, and the projects are at least partially configured to make that possible,
    // but it's not quite working yet.
    private static string DAFNY_ROOT = IS_NET_CORE ? 
      OUTPUT_ROOT.Parent.Parent.Parent.Parent.Parent.FullName :
      OUTPUT_ROOT.Parent.Parent.Parent.Parent.FullName;

    public static readonly string TEST_ROOT = Path.Combine(DAFNY_ROOT, "Test") + Path.DirectorySeparatorChar;
    public static string COMP_DIR = Path.Combine(TEST_ROOT, "comp") + Path.DirectorySeparatorChar;
    private static string OUTPUT_DIR = Path.Combine(TEST_ROOT, "Output") + Path.DirectorySeparatorChar;
    
    private static string DAFNY_EXE = Path.Combine(DAFNY_ROOT, "Binaries/Dafny.exe");
        
    public string DafnyFile;
    public string[] Arguments;
    
    // May be null if the test doesn't need to check the output
    public string ExpectedOutputFile;
    private readonly string ExpectedExitCode;

    private readonly bool SpecialCase = false;

    public DafnyTestCase(string dafnyFile, Dictionary<string, string> config, string compileTarget) {
      DafnyFile = dafnyFile;
      var fullDafnyFilePath = Path.Combine(TEST_ROOT, DafnyFile);

      config.TryGetValue("expect", out ExpectedOutputFile);
      config.Remove("expect");
      if (ExpectedOutputFile == null) {
        ExpectedOutputFile = dafnyFile + ".expect";
        if (compileTarget != null) {
          var specialCasePath = dafnyFile + "." + compileTarget + ".expect";
          if (File.Exists(Path.Combine(TEST_ROOT, specialCasePath))) {
            SpecialCase = true;
            ExpectedOutputFile = specialCasePath;
          }
        }
      } else if (ExpectedOutputFile.Equals("no")) {
        ExpectedOutputFile = null;
      }

      Arguments = config.Select(ConfigPairToArgument).ToArray();
      
      if (compileTarget != null) {
        Arguments = Arguments.Concat(new[] {"/compileTarget:" + compileTarget}).ToArray();
        // Include any additional files
        var additionalFilesPath = fullDafnyFilePath + "." + compileTarget + ".files";
        if (Directory.Exists(additionalFilesPath)) {
          var relativePaths = Directory.GetFiles(additionalFilesPath)
            .Select(path => DafnyTests.GetRelativePath(TEST_ROOT, path));
          Arguments = Arguments.Concat(relativePaths).ToArray();
        }
      }
    }

    public DafnyTestCase() {
      
    }
    
    public void Serialize(IXunitSerializationInfo info) {
      info.AddValue(nameof(DafnyFile), DafnyFile);
      info.AddValue(nameof(Arguments), Arguments);
    }
    
    public void Deserialize(IXunitSerializationInfo info) {
      DafnyFile = info.GetValue<string>(nameof(DafnyFile));
      Arguments = info.GetValue<string[]>(nameof(Arguments));
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
        dafnyProcess.StartInfo.FileName = "mono";
        dafnyProcess.StartInfo.Arguments += DAFNY_EXE;
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
                    .Select(t => new object[] {t.DafnyFile, t.Arguments, t.ExpectedOutputFile});
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
      string fullInputPath = Path.Combine(TEST_ROOT, DafnyFile);

      var arguments = new []{ fullInputPath }.Concat(Arguments);
      
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
          arguments = new []{ outArgument }.Concat(arguments);
          output = RunDafny(arguments);
        }
      }

      if (ExpectedOutputFile != null) {
        var expectedOutput = File.ReadAllText(Path.Combine(TEST_ROOT, ExpectedOutputFile));
        AssertWithDiff.Equal(expectedOutput, output);
      }

      Skip.If(SpecialCase, "Confirmed known exception for arguments: " + arguments);
    }
  }

  public class DafnyTests {
    
    public static IEnumerable<object[]> AllTestFiles() {
      var filePaths = Directory.GetFiles(DafnyTestCase.COMP_DIR, "*.dfy", SearchOption.AllDirectories)
        .Select(path => GetRelativePath(DafnyTestCase.TEST_ROOT, path));
      return filePaths.SelectMany(DafnyTestCase.TestCasesForDafnyFile);
    }

    // TODO-RS: Replace with Path.GetRelativePath() if we move to .NET Core 3.1
    public static string GetRelativePath(string relativeTo, string path) {
      var fullRelativeTo = Path.GetFullPath(relativeTo);
      var fullPath = Path.GetFullPath(path);
      Assert.StartsWith(fullRelativeTo, fullPath);
      return fullPath.Substring(fullRelativeTo.Length);
    }

    [ParallelTheory]
    [MemberData(nameof(AllTestFiles))]
    public static void Test(string dafnyFile, string[] arguments, string expectedOutputFile) {
      var testCase = new DafnyTestCase();
      testCase.DafnyFile = dafnyFile;
      testCase.Arguments = arguments;
      testCase.ExpectedOutputFile = expectedOutputFile;
      testCase.Run();
    }
  }
}