using System;
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
        private static string TEST_ROOT = Path.Combine(DAFNY_ROOT, "Test");
        private static string COMP_DIR = Path.Combine(TEST_ROOT, "comp") + Path.DirectorySeparatorChar;
        
        
        private string RunDafnyProgram(string filePath, params string[] arguments) {
            List<string> dafnyArguments = new List<string> {

                filePath,
                "/compile:3",
                
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
            return RunDafny(dafnyArguments);
        }

        public static string RunDafny(IEnumerable<string> arguments) {
            using (Process dafnyProcess = new Process()) {
                dafnyProcess.StartInfo.FileName = "mono";
                dafnyProcess.StartInfo.ArgumentList.Add(DAFNY_EXE);
                foreach (var argument in arguments) {
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

        public static IEnumerable<object[]> TestData() {
            var filePaths = Directory.GetFiles(COMP_DIR, "*.dfy")
                                     .Select(path => GetRelativePath(COMP_DIR, path));
//            var filePaths = new string[] {"NativeNumbers.dfy"};
            var languages = new string[] {"cs", "java", "go", "js"};
            foreach (var filePath in filePaths) {
                foreach (var language in languages) {
                    yield return new object[] { filePath, language };
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
        [MemberData(nameof(TestData))]
        public void ValidProgramOutput(String program, String language) {
            string fullInputPath = Path.Combine(COMP_DIR, program);
            
            string expectedOutputPath = fullInputPath + ".expect";
            string expectedLangOutputPath = fullInputPath + "." + language + ".expect";
            bool langSpecific = File.Exists(expectedLangOutputPath);
            string expectedOutput = langSpecific ? File.ReadAllText(expectedLangOutputPath) : File.ReadAllText(expectedOutputPath);
            
            string output = RunDafnyProgram(fullInputPath, "/compileTarget:" + language);
            
            AssertEqualWithDiff(expectedOutput, output);
            Skip.If(langSpecific, "Confirmed language-specific behavior");
        }
    }
}