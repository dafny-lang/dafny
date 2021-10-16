using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using Xunit.Abstractions;

namespace XUnitExtensions {
  public class MainMethodLitCommand : ILitCommand {
    public LitTestConfiguration Config { get; protected set; }
    public Assembly Assembly { get; protected set; }
    public string[] Arguments { get; protected set; }

    public static ILitCommand Parse(Assembly assembly, IEnumerable<string> arguments, LitTestConfiguration config, bool invokeDirectly) {
      var result = new MainMethodLitCommand {
        Config = config,
        Assembly = assembly,
        Arguments = arguments.ToArray()
      };

      return invokeDirectly ? result : result.ToShellCommand(config);
    }

    public (int, string, string) Execute(ITestOutputHelper outputHelper, TextReader inputReader, TextWriter outputWriter, TextWriter errorWriter) {
      if (inputReader != null) {
        Console.SetIn(inputReader);
      }
      if (outputWriter != null) {
        Console.SetOut(outputWriter);
      }
      if (errorWriter != null) {
        Console.SetError(errorWriter);
      }

      var exitCode = (int)Assembly.EntryPoint!.Invoke(null, new object[] { Arguments });

      return (exitCode, "", "");
    }

    public ILitCommand ToShellCommand(LitTestConfiguration config) {
      var shellArguments = new[] { Assembly.Location }.Concat(Arguments);
      return new ShellLitCommand(config, "dotnet", shellArguments, config.PassthroughEnvironmentVariables);
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