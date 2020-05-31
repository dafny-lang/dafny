using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using Xunit;

namespace DafnyTests {

    public class TestData : IEnumerable<object[]> {
        public IEnumerator<object[]> GetEnumerator() {
            yield return new object[] { "comp/Hello.dfy", "cs" };
        }

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    }
    
    public class DafnyTests {
        private string RunDafny(string filePath, params string[] otherArguments) {
            using (Process dafnyProcess = new Process()) {
                dafnyProcess.StartInfo.FileName = "dafny";
                dafnyProcess.StartInfo.Arguments = "/Users/salkeldr/Documents/GitHub/dafny/Test/" + filePath;
                dafnyProcess.StartInfo.Arguments += " /compile:3";
                foreach (var otherArgument in otherArguments) {
                    dafnyProcess.StartInfo.Arguments += " " + otherArgument;
                }
                dafnyProcess.StartInfo.UseShellExecute = false;
                dafnyProcess.StartInfo.RedirectStandardOutput = true;
                dafnyProcess.StartInfo.RedirectStandardError = true;
                dafnyProcess.StartInfo.CreateNoWindow = true;
                dafnyProcess.Start();
                dafnyProcess.WaitForExit();
                if (dafnyProcess.ExitCode != 0) {
                    Assert.True(false, dafnyProcess.StandardOutput.ReadToEnd());
                }
                return dafnyProcess.StandardOutput.ReadToEnd();
            }
        }
        
        [SkippableTheory()]
        [ClassData(typeof(TestData))]
        public void ValidProgramOutput(String inputPath, String targetLanguage) {
            string output = RunDafny(inputPath, "/compileTarget:" + targetLanguage);
            Console.Out.Write(output);
        }
    }
}