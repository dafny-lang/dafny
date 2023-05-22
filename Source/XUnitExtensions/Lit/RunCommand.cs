using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Extensions.FileSystemGlobbing;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public abstract class RunCommand {
    public static ILitCommand Parse(string line, LitTestConfiguration config) {
      return ParseArguments(ILitCommand.Tokenize(line), config);
    }

    private static ILitCommand ParseArguments(Token[] tokens, LitTestConfiguration config) {
      if (tokens[0].Value == "!") {
        var operand = ParseArguments(tokens[1..], config);
        return new NotCommand(operand);
      }
      if (tokens[0].Value == "%exits-with") {
        var ec = Int32.Parse(tokens[1].Value);
        var operand = ParseArguments(tokens[2..], config);
        return new ExitCommand(ec, operand);
      }
      if (tokens[0].Value == "%stdin") {
        var operand = ParseArguments(tokens[2..], config);
        return new StdInCommand(tokens[1].Value, operand);
      }


      // Just supporting || for now since it's a precise way to ignore an exit code
      var seqOperatorIndex = Array.FindIndex(tokens, t => t.Value == "||");
      if (seqOperatorIndex >= 0) {
        var lhs = LitCommandWithRedirection.Parse(tokens[0..seqOperatorIndex], config);
        var rhs = ParseArguments(tokens[(seqOperatorIndex + 1)..], config);
        return new OrCommand(lhs, rhs);
      }
      return LitCommandWithRedirection.Parse(tokens, config);
    }
  }
}
