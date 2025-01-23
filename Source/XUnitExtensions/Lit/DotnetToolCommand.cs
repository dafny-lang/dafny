using System.Collections.Generic;
using System.Linq;

namespace XUnitExtensions.Lit {

  public class DotnetToolCommand(
    string dotnetToolName,
    IEnumerable<string> arguments,
    IEnumerable<string> passthroughEnvironmentVariables)
    : ShellLitCommand("dotnet", DotnetToolArgs.Append(dotnetToolName).Concat(arguments),
      passthroughEnvironmentVariables) {

    private static readonly string[] DotnetToolArgs = ["tool", "run"];
  }
}