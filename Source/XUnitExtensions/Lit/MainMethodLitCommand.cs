using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class MainMethodLitCommand : ILitCommand {
    private readonly Assembly assembly;
    public string[] Arguments { get; }

    private MainMethodLitCommand(Assembly assembly, string[] arguments) {
      this.assembly = assembly;
      this.Arguments = arguments;
    }

    public static ILitCommand Parse(Assembly assembly, IEnumerable<string> arguments, LitTestConfiguration config, bool invokeDirectly) {
      var result = new MainMethodLitCommand(assembly, arguments.ToArray());
      return invokeDirectly ? result : result.ToShellCommand(config);
    }

    public (int, string, string) Execute(TextReader inputReader,
      TextWriter outputWriter, TextWriter errorWriter) {
      if (inputReader != null) {
        Console.SetIn(inputReader);
      }
      if (outputWriter != null) {
        Console.SetOut(outputWriter);
      }
      if (errorWriter != null) {
        Console.SetError(errorWriter);
      }

      var result = assembly.EntryPoint!.Invoke(null, new object[] { Arguments });
      var exitCode = result == null ? 0 : (int)result;

      return (exitCode, "", "");
    }

    public ILitCommand ToShellCommand(LitTestConfiguration config) {
      var shellArguments = new[] { assembly.Location }.Concat(Arguments);
      return new ShellLitCommand("dotnet", shellArguments, config.PassthroughEnvironmentVariables);
    }

    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(assembly.EntryPoint);
      builder.Append(' ');
      builder.AppendJoin(" ", Arguments);
      return builder.ToString();
    }
  }
}
