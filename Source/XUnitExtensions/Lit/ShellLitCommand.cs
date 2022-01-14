using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class ShellLitCommand : ILitCommand {
    private LitTestConfiguration config;
    private string shellCommand;
    private string[] arguments;
    private string[] passthroughEnvironmentVariables;

    public ShellLitCommand(LitTestConfiguration config, string shellCommand, IEnumerable<string> arguments, IEnumerable<string> passthroughEnvironmentVariables) {
      this.config = config;
      this.shellCommand = shellCommand;
      this.arguments = arguments.ToArray();
      this.passthroughEnvironmentVariables = passthroughEnvironmentVariables.ToArray();
    }

    public (int, string, string) Execute(ITestOutputHelper outputHelper, TextReader? inputReader, TextWriter? outputWriter, TextWriter? errorWriter) {
      using var process = new Process();

      process.StartInfo.FileName = shellCommand;
      foreach (var argument in arguments) {
        process.StartInfo.ArgumentList.Add(argument);
      }

      // We avoid setting the current directory so that we maintain parity with
      // MainMethodLitCommand, which can't change the current directory.

      process.StartInfo.UseShellExecute = false;
      process.StartInfo.RedirectStandardInput = true;
      process.StartInfo.RedirectStandardOutput = true;
      process.StartInfo.RedirectStandardError = true;
      process.StartInfo.CreateNoWindow = true;

      process.StartInfo.EnvironmentVariables.Clear();
      foreach (var passthrough in passthroughEnvironmentVariables) {
        process.StartInfo.EnvironmentVariables.Add(passthrough, Environment.GetEnvironmentVariable(passthrough));
      }

      process.Start();
      if (inputReader != null) {
        string input = inputReader.ReadToEnd();
        inputReader.Close();
        process.StandardInput.Write(input);
        process.StandardInput.Close();
      }
      string output = process.StandardOutput.ReadToEnd();
      outputWriter?.Write(output);
      outputWriter?.Close();
      string error = process.StandardError.ReadToEnd();
      errorWriter?.Write(error);
      errorWriter?.Close();
      process.WaitForExit();

      return (process.ExitCode, output, error);
    }

    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(shellCommand);
      builder.Append(' ');
      builder.AppendJoin(" ", arguments);
      return builder.ToString();
    }
  }
}