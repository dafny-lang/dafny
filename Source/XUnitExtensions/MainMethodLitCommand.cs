using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;

namespace XUnitExtensions {
  public class MainMethodLitCommand : ILitCommand {
    public Assembly Assembly { get; protected set; }
    public string[] Arguments { get; protected set; }
    public string OutputFile { get; protected set; }
    public bool AppendOutput { get; protected set; }

    public static ILitCommand Parse(Assembly assembly, IEnumerable<string> arguments, LitTestConfiguration config) {
      var result = new MainMethodLitCommand {
        Assembly = assembly
      };

      var argumentsList = arguments.ToList();
      var redirectIndex = argumentsList.IndexOf(">");
      if (redirectIndex >= 0) {
        result.OutputFile = argumentsList[redirectIndex + 1];
        argumentsList.RemoveRange(redirectIndex, 2);
      }
      var redirectAppendIndex = argumentsList.IndexOf(">>");
      if (redirectAppendIndex >= 0) {
        result.OutputFile = argumentsList[redirectAppendIndex + 1];
        result.AppendOutput = true;
        argumentsList.RemoveRange(redirectAppendIndex, 2);
      }

      return config.InvokeMainMethodsDirectly ? result : result.ToShellCommand(config);
    }

    public (int, string) Execute() {
      StringBuilder redirectedErr = new();

      if (OutputFile != null) {
        Console.SetOut(new StreamWriter(OutputFile, append: AppendOutput));
      }
      Console.SetError(new StringWriter(redirectedErr));

      var exitCode = (int)Assembly.EntryPoint!.Invoke(null, new object[] { Arguments });
      
      return (exitCode, redirectedErr.ToString());
    }

    public ILitCommand ToShellCommand(LitTestConfiguration config) {
      var shellArguments = new[] { Assembly.Location }.Concat(Arguments);
      if (OutputFile != null) {
        shellArguments = shellArguments.Append(AppendOutput ? ">>" : ">").Append(OutputFile);
      }
      return new ShellLitCommand("dotnet", shellArguments, config.PassthroughEnvironmentVariables);
    }
    
    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(Assembly);
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
  }
}