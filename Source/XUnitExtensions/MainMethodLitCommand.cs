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

    public static ILitCommand Parse(Assembly assembly, IEnumerable<string> arguments, LitTestConfiguration config, bool invokeDirectly) {
      var result = new MainMethodLitCommand {
        Assembly = assembly,
        Arguments = arguments.ToArray()
      };

      return invokeDirectly ? result : result.ToShellCommand(config);
    }

    public (int, string, string) Execute(TextWriter outputWriter) {
      StringBuilder redirectedErr = new();

      if (outputWriter != null) {
        Console.SetOut(outputWriter);
      }
      Console.SetError(new StringWriter(redirectedErr));

      var exitCode = (int)Assembly.EntryPoint!.Invoke(null, new object[] { Arguments });
      
      return (exitCode, "", redirectedErr.ToString());
    }

    public ILitCommand ToShellCommand(LitTestConfiguration config) {
      var shellArguments = new[] { Assembly.Location }.Concat(Arguments);
      return new ShellLitCommand("dotnet", shellArguments, config.PassthroughEnvironmentVariables);
    }
    
    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(Assembly.EntryPoint);
      builder.Append(' ');
      builder.AppendJoin(" ", Arguments);
      return builder.ToString();
    }
  }
}