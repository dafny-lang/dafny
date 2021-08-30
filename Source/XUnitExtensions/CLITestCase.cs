using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions {

  public class CLITestCase : IXunitSerializable {
    protected Assembly CliAssembly;
    protected string CliAssemblyName;
    protected bool InvokeDirectly;

    protected string[] Arguments;
    protected IEnumerable<string> PassthroughEnvironmentVariables;
    protected Expectation Expected;

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

    public CLITestCase(Assembly cliAssembly, IEnumerable<string> arguments,
                       IEnumerable<string> passthroughEnvironmentVariables,
                       Expectation expected, bool invokeDirectly) {
      CliAssembly = cliAssembly;
      Arguments = arguments.ToArray();
      PassthroughEnvironmentVariables = passthroughEnvironmentVariables;
      Expected = expected;
      InvokeDirectly = invokeDirectly;
    }

    public CLITestCase() {

    }

    public void Serialize(IXunitSerializationInfo info) {
      info.AddValue(nameof(CliAssemblyName), CliAssemblyName);
      info.AddValue(nameof(Arguments), Arguments);
      info.AddValue(nameof(Expected), Expected);
    }

    public void Deserialize(IXunitSerializationInfo info) {
      CliAssemblyName = info.GetValue<string>(nameof(CliAssemblyName));
      CliAssembly = AppDomain.CurrentDomain.GetAssemblies().First(a => a.FullName == CliAssemblyName);

      Arguments = info.GetValue<string[]>(nameof(Arguments));
      Expected = info.GetValue<Expectation>(nameof(Expected));
    }

    public CLIResult InvokeCLI() {
      if (InvokeDirectly || Environment.GetEnvironmentVariable("XUNIT_INVOKE_CLI_DIRECTLY") == "true") {
        return InvokeCLIDirectly();
      }
      return InvokeCLIViaProcess();
    }

    public CLIResult InvokeCLIDirectly() {
      StringBuilder redirectedOut = new();
      StringBuilder redirectedErr = new();

      Console.SetOut(new StringWriter(redirectedOut));
      Console.SetError(new StringWriter(redirectedErr));

      int result = (int)CliAssembly.EntryPoint.Invoke(null, new object[] { Arguments });

      return new CLIResult(result, redirectedOut.ToString(), redirectedErr.ToString());
    }

    public CLIResult InvokeCLIViaProcess() {
      using var process = new Process();

      process.StartInfo.FileName = "dotnet";
      process.StartInfo.Arguments = CliAssembly.Location;
      foreach (var argument in Arguments) {
        process.StartInfo.Arguments += " " + argument;
      }

      process.StartInfo.UseShellExecute = false;
      process.StartInfo.RedirectStandardOutput = true;
      process.StartInfo.RedirectStandardError = true;
      process.StartInfo.CreateNoWindow = true;

      process.StartInfo.EnvironmentVariables.Clear();
      foreach (var passthrough in PassthroughEnvironmentVariables) {
        process.StartInfo.EnvironmentVariables.Add(passthrough, Environment.GetEnvironmentVariable(passthrough));
      }

      process.Start();
      string output = process.StandardOutput.ReadToEnd();
      string error = process.StandardError.ReadToEnd();
      process.WaitForExit();

      return new CLIResult(process.ExitCode, output, error);
    }

    public void Run() {
      CLIResult result = InvokeCLI();

      if (result.ExitCode != Expected.ExitCode) {
        throw new AssertActualExpectedException(Expected.ExitCode, result.ExitCode,
          String.Format("Expected exit code to be {0} but was {1}. Standard error output:\n{2}",
            Expected.ExitCode, result.ExitCode, result.StandardError));
      }
      if (Expected.OutputFile != null) {
        var expectedOutput = File.ReadAllText(Expected.OutputFile);
        AssertWithDiff.Equal(expectedOutput, result.StandardOutput);
      }

      Skip.If(Expected.SpecialCaseReason != null, Expected.SpecialCaseReason);
    }

    public override string ToString() {
      return String.Join(" ", Arguments) + " => " + Expected;
    }
  }
}
