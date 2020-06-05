using System;
using System.Linq;
using System.CodeDom.Compiler;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using DiffMatchPatch;
using Microsoft.Extensions.DependencyModel;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using Assert = Xunit.Assert;

namespace DafnyTests {

    public class DafnyTests {

        private static string DAFNY_ROOT = new DirectoryInfo(Directory.GetCurrentDirectory()).Parent.Parent.Parent.Parent.Parent.FullName;
        private static string DAFNY_EXE = Path.Combine(DAFNY_ROOT, "Binaries/Dafny.exe");
        private static string TEST_ROOT = Path.Combine(DAFNY_ROOT, "Test") + Path.DirectorySeparatorChar;
        private static string COMP_DIR = Path.Combine(TEST_ROOT, "comp") + Path.DirectorySeparatorChar;
        
        
        public static string RunDafny(IEnumerable<string> arguments) {
            List<string> dafnyArguments = new List<string> {
                // Expected output does not contain logo
                "-nologo",
                "-countVerificationErrors:0",

                // We do not want absolute or relative paths in error messages, just the basename of the file
                "-useBaseNameForFileName",

                // We do not want output such as "Compiled program written to Foo.cs"
                // from the compilers, since that changes with the target language
                "-compileVerbose:0"
            };
            dafnyArguments.AddRange(arguments);
            
            using (Process dafnyProcess = new Process()) {
                dafnyProcess.StartInfo.FileName = "mono";
                dafnyProcess.StartInfo.ArgumentList.Add(DAFNY_EXE);
                foreach (var argument in dafnyArguments) {
                    dafnyProcess.StartInfo.ArgumentList.Add(argument);
                }

                dafnyProcess.StartInfo.UseShellExecute = false;
                dafnyProcess.StartInfo.RedirectStandardOutput = true;
                dafnyProcess.StartInfo.RedirectStandardError = true;
                dafnyProcess.StartInfo.CreateNoWindow = true;
                // Necessary for JS to find bignumber.js
                dafnyProcess.StartInfo.WorkingDirectory = TEST_ROOT;
                
                // Only preserve specific whitelisted environment variables
                dafnyProcess.StartInfo.EnvironmentVariables.Clear();
                dafnyProcess.StartInfo.EnvironmentVariables.Add("PATH", System.Environment.GetEnvironmentVariable("PATH"));
                // Go requires this or GOCACHE
                dafnyProcess.StartInfo.EnvironmentVariables.Add("HOME", System.Environment.GetEnvironmentVariable("HOME"));

                dafnyProcess.Start();
                dafnyProcess.WaitForExit();
                string output = dafnyProcess.StandardOutput.ReadToEnd();
                string error = dafnyProcess.StandardError.ReadToEnd();
                if (dafnyProcess.ExitCode != 0) {
                    Assert.True(false, output + "\n" + error);
                }

                return output + error;
            }
        }

        public static IEnumerable<object[]> AllTestFiles() {
            var filePaths = Directory.GetFiles(TEST_ROOT, "*.dfy", SearchOption.AllDirectories)
                                     .Select(path => GetRelativePath(TEST_ROOT, path));
            foreach (var filePath in filePaths) {
                // Parse the arguments to testdafny on the "shebang" line
                // TODO: override with environment variable from testdafny itself when executed
                string shebang = File.ReadLines(Path.Combine(TEST_ROOT, filePath)).FirstOrDefault();
                int semiIndex = shebang.IndexOf(";");
                if (semiIndex >= 0) {
                    string[] chunks = shebang.Substring(0, semiIndex).Split();
                    List<string> arguments = chunks.Skip(3).ToList();

                    if (!arguments.Any(arg => arg.StartsWith("/compile:"))) {
                        var languages = new string[] {"cs", "java", "go", "js"};
                        foreach (var language in languages) {
                            yield return new object[]
                                {filePath, arguments.Concat(new[] {"/compile:3", "/compileTarget:" + language}).ToArray()};
                        }
                    } else {
                        yield return new object[] {filePath, arguments};
                    }
                } else {
                    yield return new object[] {filePath, new[] { "/compile:0" }};
                }
            }
        }

        // TODO-RS: Replace with Path.GetRelativePath() if we move to .NET Core 3.1
        private static string GetRelativePath(string relativeTo, string path) {
            var fullRelativeTo = Path.GetFullPath(relativeTo);
            var fullPath = Path.GetFullPath(path);
            Assert.StartsWith(fullRelativeTo, fullPath);
            return fullPath.Substring(fullRelativeTo.Length);
        }

        private static void AssertEqualWithDiff(string expected, string actual) {
            if (expected != actual) {
                DiffMatchPatch.DiffMatchPatch dmp = DiffMatchPatchModule.Default;
                List<Diff> diff = dmp.DiffMain(expected, actual);
                dmp.DiffCleanupSemantic(diff);
                string patch = DiffText(diff);
                throw new AssertActualExpectedException(expected, actual, patch);
            }
        }

        private static string DiffText(List<Diff> diffs) {
            return "";
        }
        
        [ParallelTheory]
        [MemberData(nameof(AllTestFiles))]
        public void Test(string file, string[] args) {
            string fullInputPath = Path.Combine(TEST_ROOT, file);
            
            string expectedOutputPath = fullInputPath + ".expect";
            bool specialCase = false;
            string compileTarget = args.FirstOrDefault(arg => arg.StartsWith("/compileTarget:"));
            if (compileTarget != null) {
                string language = compileTarget.Substring("/compileTarget:".Length);
                var specialCasePath = fullInputPath + "." + language + ".expect";
                if (File.Exists(specialCasePath)) {
                    specialCase = true;
                    expectedOutputPath = specialCasePath;
                }
            }
            string expectedOutput = File.ReadAllText(expectedOutputPath);

            string output = RunDafny(new List<string>{ fullInputPath }.Concat(args));
            
            AssertEqualWithDiff(expectedOutput, output);
            Skip.If(specialCase, "Confirmed known exception for arguments: " + args);
        }
    }
}