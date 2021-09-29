using System;
using System.Linq;
using System.Reflection;

namespace XUnitExtensions {
  public interface ILitCommand {
    
    private const string COMMENT_PREFIX = "//";
    private const string LIT_COMMAND_PREFIX = "RUN:";

    public (int, string) Execute();
    
    public static ILitCommand Parse(string line, LitTestConfiguration config) {
      if (!line.StartsWith(COMMENT_PREFIX)) {
        return null;
      }
      line = line[COMMENT_PREFIX.Length..].Trim();

      if (!line.StartsWith(LIT_COMMAND_PREFIX)) {
        return null;
      }
      line = line[LIT_COMMAND_PREFIX.Length..].Trim();
      
      // TODO: Probably need to handle escaping too
      var pieces = line.Split((char[])null, StringSplitOptions.RemoveEmptyEntries);
      var commandSymbol = pieces[0];
      var arguments = pieces[1..];

      if (config.MainMethodSubstitutions.TryGetValue(commandSymbol, out (Assembly, string[]) substitution)) {
        return MainMethodLitCommand.Parse(substitution.Item1, substitution.Item2.Concat(arguments), config);
      }

      return new ShellLitCommand(commandSymbol, arguments, config.PassthroughEnvironmentVariables);
    }
  }
}