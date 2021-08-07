using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using DafnyDriver.Test.XUnitExtensions;
using Microsoft.Extensions.FileProviders;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using XUnitExtensions;
using YamlDotNet.Core;
using YamlDotNet.Serialization;
using YamlDotNet.Serialization.NamingConventions;
using YamlDotNet.Serialization.ObjectFactories;

namespace DafnyDriver.Test {
  
  // TODO-RS: This is really close to a generic CLI test case -
  // can we move all the dafny-specific stuff to DafnyTestSpec instead?
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
        "/countVerificationErrors:0",

        // We do not want absolute or relative paths in error messages, just the basename of the file
        "/useBaseNameForFileName",

        // We do not want output such as "Compiled program written to Foo.cs"
        // from the compilers, since that changes with the target language
        "/compileVerbose:0"
      };
      dafnyArguments.AddRange(arguments);

      using (Process dafnyProcess = new Process()) {
        dafnyProcess.StartInfo.FileName = "dotnet";
        dafnyProcess.StartInfo.Arguments = "run --no-build --project ";
        dafnyProcess.StartInfo.Arguments += DafnyTestSpec.DAFNY_PROJ;
        dafnyProcess.StartInfo.Arguments += " --";
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
        string output = dafnyProcess.StandardOutput.ReadToEnd();
        string error = dafnyProcess.StandardError.ReadToEnd();
        dafnyProcess.WaitForExit();
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
}
