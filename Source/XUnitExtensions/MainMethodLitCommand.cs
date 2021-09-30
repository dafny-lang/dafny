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
        Assembly = assembly,
      };

      IEnumerable<string> args;
      (args, result.OutputFile, result.AppendOutput) = ILitCommand.ExtractOutputFile(arguments);
      result.Arguments = args.ToArray();
      
      return config.InvokeMainMethodsDirectly ? result : result.ToShellCommand(config);
    }

    public (int, string, string) Execute() {
      StringBuilder redirectedErr = new();

      if (OutputFile != null) {
        Console.SetOut(new StreamWriter(OutputFile, append: AppendOutput));
      }
      Console.SetError(new StringWriter(redirectedErr));

      var exitCode = (int)Assembly.EntryPoint!.Invoke(null, new object[] { Arguments });
      
      return (exitCode, "", redirectedErr.ToString());
    }

    public ILitCommand ToShellCommand(LitTestConfiguration config) {
      var shellArguments = new[] { Assembly.Location }.Concat(Arguments);
      return new ShellLitCommand("dotnet", shellArguments, OutputFile, AppendOutput, config.PassthroughEnvironmentVariables);
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