using System;
using System.IO;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public abstract class RunCommand {
    public static ILitCommand Parse(string line, LitTestConfiguration config) {
      return ParseArguments(ILitCommand.Tokenize(line), config);
    }

    private static ILitCommand ParseArguments(string[] tokens, LitTestConfiguration config) {
      // Just supporting || for now since it's a precise way to ignore an exit code
      var seqOperatorIndex = Array.IndexOf(tokens, "||");
      if (seqOperatorIndex >= 0) {
        var lhs = LitCommandWithRedirection.Parse(tokens[0..seqOperatorIndex], config);
        var rhs = ParseArguments(tokens[(seqOperatorIndex + 1)..], config);
        return new OrCommand(lhs, rhs);
      }
      return LitCommandWithRedirection.Parse(tokens, config);
    }
  }
}