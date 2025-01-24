using System.Collections.Generic;
using System.Linq;

namespace XUnitExtensions.Lit {

  public class DotnetToolCommand : ShellLitCommand {

    private static readonly string[] DotnetToolArgs = ["tool", "run"];

    public DotnetToolCommand(string dotnetToolName, IEnumerable<string> arguments, IEnumerable<string> passthroughEnvironmentVariables) :
      base("dotnet", DotnetToolArgs.Append(dotnetToolName).Concat(arguments), passthroughEnvironmentVariables) { }
  }
}