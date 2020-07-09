using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using DiffPlex;
using DiffPlex.DiffBuilder;
using DiffPlex.DiffBuilder.Model;
using Xunit;
using Xunit.Sdk;
using XUnitExtensions;
using YamlDotNet.RepresentationModel;
using YamlDotNet.Serialization;

namespace DafnyTests {

  public class DafnyTests {

    private static DirectoryInfo OUTPUT_ROOT = new DirectoryInfo(Directory.GetCurrentDirectory());
    private static string DAFNY_ROOT = OUTPUT_ROOT.Parent.Parent.Parent.Parent.FullName;

    private static string TEST_ROOT = Path.Combine(DAFNY_ROOT, "Test") + Path.DirectorySeparatorChar;
    private static string COMP_DIR = Path.Combine(TEST_ROOT, "comp") + Path.DirectorySeparatorChar;
    private static string OUTPUT_DIR = Path.Combine(TEST_ROOT, "Output") + Path.DirectorySeparatorChar;

    private static string DAFNY_EXE = Path.Combine(DAFNY_ROOT, "Binaries/Dafny.exe");
        
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
    public static IEnumerable<object[]> AllTestFiles() {
      var filePaths = Directory.GetFiles(COMP_DIR, "*.dfy", SearchOption.AllDirectories)
        .Select(path => GetRelativePath(TEST_ROOT, path));
      return filePaths.SelectMany(TestCasesForDafnyFile);
    }

    private static IEnumerable<object[]> TestCasesForDafnyFile(string filePath) {
      var fullFilePath = Path.Combine(TEST_ROOT, filePath);
      string configString = GetTestCaseConfigString(fullFilePath);
      IEnumerable<YamlNode> configs;
      if (configString != null) {
        var yamlStream = new YamlStream();
        yamlStream.Load(new StringReader(configString));
        var config = yamlStream.Documents[0].RootNode;
        configs = YamlUtils.Expand(config);
      } else {
        configs = new[] {new YamlMappingNode()};
      }

      IEnumerable<YamlMappingNode> mappings = configs.SelectMany<YamlNode, YamlMappingNode>(config => {
        if (config is YamlMappingNode mapping) {
          return ResolveCompile(filePath, mapping);
        } else {
          throw new ArgumentException("Bad test case configuration: " + config);
        }
      });

      return mappings.Select(mapping => {
        return new[] {filePath, String.Join(" ", mapping.Select(ConfigPairToArgument))};
      });
    }

    private static IEnumerable<YamlMappingNode> ResolveCompile(string filePath, YamlMappingNode mapping) {
      if (!mapping.Children.ContainsKey(new YamlScalarNode("compile"))) {
        mapping.Add("compile", "3");
      }

      if (mapping["compile"].Equals(new YamlScalarNode("3")) && !mapping.Children.ContainsKey("compileTarget")) {
        var languages = new[] {"cs", "java", "go", "js"};
        foreach (var language in languages) {
          var withLanguage = new YamlMappingNode(mapping.Children);
          withLanguage.Add("compileTarget", language);
          yield return withLanguage;
        }
      } else {
        yield return mapping;
      }
    }

    private static string ConfigPairToArgument(KeyValuePair<YamlNode, YamlNode> pair) {
      if (pair.Key.Equals(new YamlScalarNode("otherFiles"))) {
        return pair.Value.ToString();
      } else {
        return String.Format("/{0}:{1}", pair.Key, pair.Value);
      }
    }

    // TODO-RS: Replace with Path.GetRelativePath() if we move to .NET Core 3.1
    private static string GetRelativePath(string relativeTo, string path) {
      var fullRelativeTo = Path.GetFullPath(relativeTo);
      var fullPath = Path.GetFullPath(path);
      Assert.StartsWith(fullRelativeTo, fullPath);
      return fullPath.Substring(fullRelativeTo.Length);
    }

    [ParallelTheory]
    [MemberData(nameof(AllTestFiles))]
    public void Test(string file, string args) {
      string fullInputPath = Path.Combine(TEST_ROOT, file);
      string[] arguments = args.Split();

      string expectedOutputPath = fullInputPath + ".expect";
      bool specialCase = false;
      string compileTarget = arguments.FirstOrDefault(arg => arg.StartsWith("/compileTarget:"));
      if (compileTarget != null) {
        string language = compileTarget.Substring("/compileTarget:".Length);
        var specialCasePath = fullInputPath + "." + language + ".expect";
        if (File.Exists(specialCasePath)) {
          specialCase = true;
          expectedOutputPath = specialCasePath;
        }
                
        // Include any additional files
        var additionalFilesPath = fullInputPath + "." + language + ".files";
        if (Directory.Exists(additionalFilesPath)) {
          arguments = arguments.Concat(Directory.GetFiles(additionalFilesPath)).ToArray();
        }
      }
            
      var argumentsWithFile = new List<string> {fullInputPath}.Concat(arguments);
      var expectedOutput = File.ReadAllText(expectedOutputPath);

      string output;
      if (arguments.Any(arg => arg.StartsWith("/out"))) {
        output = RunDafny(argumentsWithFile);
      } else {
        // Note that the temporary directory has to be an ancestor of Test
        // or else Javascript won't be able to locate bignumber.js :(
        using (var tempDir = new TemporaryDirectory(OUTPUT_DIR)) {
          // Add an extra component to the path to keep the files created inside the
          // temporary directory, since some compilers will
          // interpret the path as a single file basename rather than a directory.
          var outArgument = "/out:" + tempDir.DirInfo.FullName + "/Program";
          argumentsWithFile = new List<string> {outArgument}.Concat(argumentsWithFile);
          output = RunDafny(argumentsWithFile);
        }
      }

      AssertWithDiff.Equal(expectedOutput, output);
      Skip.If(specialCase, "Confirmed known exception for arguments: " + args);
    }
  }
}