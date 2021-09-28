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

  public class LitTestCommand {
    
    private const string COMMENT_PREFIX = "//";
    private const string LIT_COMMAND_PREFIX = "RUN:";
    
    // This may be a symbol for substitution such as "%dafny"
    private string CliPath;
    private string[] Arguments;
    private string OutputFile;
    private bool AppendOutput;
    
    public LitTestCommand(string cliPath, IEnumerable<string> arguments, string outputFile, bool appendOutput) {
      CliPath = cliPath;
      Arguments = arguments.ToArray();
      OutputFile = outputFile;
      AppendOutput = appendOutput;
    }

    public void Run(LitTestConfiguration config) {
      var cliTarget = config.Substitions[CliPath];
      int result;
      if (cliTarget is Assembly assembly && 
          (config.InvokeMainMethodsDirectly || Environment.GetEnvironmentVariable("XUNIT_INVOKE_CLI_DIRECTLY") == "true")) {
        result = InvokeCLIDirectly(assembly, config);
      } else {
        result = InvokeCLIViaProcess(config);
      }
      Assert.Equal(0, result);
    }

    public int InvokeCLIDirectly(Assembly assembly, LitTestConfiguration config) {
      StringBuilder redirectedOut = new();
      StringBuilder redirectedErr = new();

      Console.SetOut(new StringWriter(redirectedOut));
      Console.SetError(new StringWriter(redirectedErr));

      return (int)assembly.EntryPoint!.Invoke(null, new object[] { ArgumentsWithSubstitutions(config) });
    }

    public int InvokeCLIViaProcess(LitTestConfiguration config) {
      using var process = new Process();

      var cliTarget = config.Substitions[CliPath];
      if (cliTarget is Assembly assembly) {
        process.StartInfo.FileName = "dotnet";
        process.StartInfo.Arguments = assembly.Location;
      } else {
        process.StartInfo.FileName = cliTarget != null ? (string)cliTarget : CliPath;
      }
      
      foreach (var argument in ArgumentsWithSubstitutions(config)) {
        process.StartInfo.Arguments += " " + argument;
      }

      process.StartInfo.UseShellExecute = false;
      // process.StartInfo.RedirectStandardOutput = true;
      // process.StartInfo.RedirectStandardError = true;
      process.StartInfo.CreateNoWindow = true;

      process.StartInfo.EnvironmentVariables.Clear();
      foreach (var passthrough in config.PassthroughEnvironmentVariables) {
        process.StartInfo.EnvironmentVariables.Add(passthrough, Environment.GetEnvironmentVariable(passthrough));
      }

      process.Start();
      process.WaitForExit();

      return process.ExitCode;
    }

    private object ApplySubstitution(string key, LitTestConfiguration config) {
      if (config.Substitions.TryGetValue(key, out var value)) {
        return value;
      }
      return key;
    }
    
    private IEnumerable<string> ArgumentsWithSubstitutions(LitTestConfiguration config) {
      return Arguments.Select(argument => (string)ApplySubstitution(argument, config));
    }
    
    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(CliPath);
      builder.Append(' ');
      builder.AppendJoin(" ", Arguments);
      if (OutputFile != null) {
        if (AppendOutput) {
          builder.Append(" >> ");
        } else {
          builder.Append(" > ");
        }
        builder.Append(OutputFile);
      }

      return builder.ToString();
    }

    public static LitTestCommand Parse(string line) {
      if (!line.StartsWith(COMMENT_PREFIX)) {
        return null;
      }
      line = line.Substring(COMMENT_PREFIX.Length).Trim();

      if (!line.StartsWith(LIT_COMMAND_PREFIX)) {
        return null;
      }
      line = line.Substring(LIT_COMMAND_PREFIX.Length).Trim();
      
      // TODO: Probably need to handle escaping too
      var pieces = line.Split((char[])null, StringSplitOptions.RemoveEmptyEntries).ToList();
      var cliPath = pieces[0];
      var arguments = pieces.GetRange(1, pieces.Count - 1);

      string outputFile = null;
      bool appendOutput = false;
      var redirectIndex = arguments.IndexOf(">");
      if (redirectIndex >= 0) {
        outputFile = arguments[redirectIndex + 1];
        arguments.RemoveRange(redirectIndex, 2);
      }
      var redirectAppendIndex = arguments.IndexOf(">>");
      if (redirectAppendIndex >= 0) {
        outputFile = arguments[redirectAppendIndex + 1];
        appendOutput = true;
        arguments.RemoveRange(redirectAppendIndex, 2);
      }

      return new LitTestCommand(cliPath, arguments, outputFile, appendOutput);
    }
  }
}
