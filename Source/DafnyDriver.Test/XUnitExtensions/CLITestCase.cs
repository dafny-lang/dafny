using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using XUnitExtensions;

namespace DafnyDriver.Test.XUnitExtensions {
  
  public class CLITestCase: IXunitSerializable
  {
    public string CLIPath;
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

    public class CLIResult {

      public int ExitCode;
      public string StandardOutput;
      public string StandardError;

      public CLIResult(int exitCode, string standardOutput, string standardError) {
        ExitCode = exitCode;
        StandardOutput = standardOutput;
        StandardError = standardError;
      }
    }

    public Expectation Expected;

    public CLITestCase(string cliPath, IEnumerable<string> arguments, Expectation expected) {
      CLIPath = cliPath;
      Arguments = arguments.ToArray();
      Expected = expected;
    }

    public CLITestCase() {
      
    }
  
    public void Serialize(IXunitSerializationInfo info) {
      info.AddValue(nameof(Arguments), Arguments);
      info.AddValue(nameof(Expected), Expected);
    }
    
    public void Deserialize(IXunitSerializationInfo info) {
      Arguments = info.GetValue<string[]>(nameof(Arguments));
      Expected = info.GetValue<Expectation>(nameof(Expected));
    }

    public CLIResult RunDafny(IEnumerable<string> arguments) {
      using (Process process = new Process()) {
        process.StartInfo.FileName = CLIPath;
        foreach (var argument in arguments) {
          process.StartInfo.Arguments += " " + argument;
        }
        
        process.StartInfo.UseShellExecute = false;
        process.StartInfo.RedirectStandardOutput = true;
        process.StartInfo.RedirectStandardError = true;
        process.StartInfo.CreateNoWindow = true;
        // Necessary for JS to find bignumber.js
        process.StartInfo.WorkingDirectory = DafnyTestSpec.TEST_ROOT;

        // Only preserve specific whitelisted environment variables
        process.StartInfo.EnvironmentVariables.Clear();
        process.StartInfo.EnvironmentVariables.Add("PATH", Environment.GetEnvironmentVariable("PATH"));
        // Go requires this or GOCACHE
        process.StartInfo.EnvironmentVariables.Add("HOME", Environment.GetEnvironmentVariable("HOME"));

        process.Start();
        string output = process.StandardOutput.ReadToEnd();
        string error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        return new CLIResult(process.ExitCode, output, error);
      }
    }

    public void Run() {
      CLIResult result;
      if (Arguments.Any(arg => arg.StartsWith("/out"))) {
        result = RunDafny(Arguments);
      } else {
        // Note that the temporary directory has to be an ancestor of Test
        // or else Javascript won't be able to locate bignumber.js :(
        using var tempDir = new TemporaryDirectory(DafnyTestSpec.OUTPUT_DIR);
          
        // Add an extra component to the path to keep the files created inside the
        // temporary directory, since some compilers will
        // interpret the path as a single file basename rather than a directory.
        var outArgument = "/out:" + tempDir.DirInfo.FullName + "/Program";
        var dafnyArguments = Arguments.Concat(new []{ outArgument });
        result = RunDafny(dafnyArguments);
      }

      if (result.ExitCode != Expected.ExitCode) {
        throw new AssertActualExpectedException(Expected.ExitCode, result.ExitCode,
          String.Format("Expected exit code to be {0} but was {1}. Standard error output:\n{2}",
            Expected.ExitCode, result.ExitCode, result.StandardError));
      }
      if (Expected.OutputFile != null) {
        var expectedOutput = File.ReadAllText(Path.Combine(DafnyTestSpec.TEST_ROOT, Expected.OutputFile));
        AssertWithDiff.Equal(expectedOutput, result.StandardOutput);
      }

      Skip.If(Expected.SpecialCaseReason != null, Expected.SpecialCaseReason);
    }

    public override string ToString() {
      return String.Join(" ", Arguments) + " => " + Expected;
    }
  }
}
