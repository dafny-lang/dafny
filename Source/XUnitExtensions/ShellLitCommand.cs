using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;

namespace XUnitExtensions {
  public class ShellLitCommand : ILitCommand {
    private string ShellCommand;
    private string[] Arguments;
    private string[] PassthroughEnvironmentVariables;

    public ShellLitCommand(string shellCommand, IEnumerable<string> arguments, IEnumerable<string> passthroughEnvironmentVariables) {
      ShellCommand = shellCommand;
      Arguments = arguments.ToArray();
      PassthroughEnvironmentVariables = passthroughEnvironmentVariables.ToArray();
    }
    
    public (int, string) Execute() {
      using var process = new Process();

      process.StartInfo.FileName = ShellCommand;
      foreach (var argument in Arguments) {
        process.StartInfo.Arguments += " " + argument;
      }

      process.StartInfo.UseShellExecute = false;
      // process.StartInfo.RedirectStandardOutput = true;
      process.StartInfo.RedirectStandardError = true;
      process.StartInfo.CreateNoWindow = true;

      process.StartInfo.EnvironmentVariables.Clear();
      foreach (var passthrough in PassthroughEnvironmentVariables) {
        process.StartInfo.EnvironmentVariables.Add(passthrough, Environment.GetEnvironmentVariable(passthrough));
      }

      process.Start();
      string error = process.StandardError.ReadToEnd();
      process.WaitForExit();

      return (process.ExitCode, error);
    }
    
    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(ShellCommand);
      builder.Append(' ');
      builder.AppendJoin(" ", Arguments);
      return builder.ToString();
    }
  }
}