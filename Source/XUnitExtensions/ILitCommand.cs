using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;

namespace XUnitExtensions {
  public interface ILitCommand {
    
    private const string COMMENT_PREFIX = "//";
    private const string LIT_COMMAND_PREFIX = "RUN:";

    public (int, string, string) Execute();
    
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
      var pieces = line.Split((char[])null, StringSplitOptions.RemoveEmptyEntries).Select(StripQuotes).ToArray();
      var commandSymbol = pieces[0];
      var arguments = pieces[1..].Select(config.ApplySubstitutions);

      if (config.MainMethodSubstitutions.TryGetValue(commandSymbol, out (Assembly, string[]) substitution)) {
        return MainMethodLitCommand.Parse(substitution.Item1, substitution.Item2.Concat(arguments), config);
      }

      commandSymbol = config.ApplySubstitutions(commandSymbol);

      return ShellLitCommand.Parse(commandSymbol, arguments, config);
    }

    private static string StripQuotes(string s) {
      if (s.Length >= 2 && s[0] == '"' && s[^1] == '"') {
        return s[1..^1];
      }
      return s;
    }
    
    public static (IEnumerable<string>, string, bool) ExtractOutputFile(IEnumerable<string> arguments) {
      var argumentsList = arguments.ToList();
      var redirectIndex = argumentsList.IndexOf(">");
      if (redirectIndex >= 0) {
        var outputFile = argumentsList[redirectIndex + 1];
        argumentsList.RemoveRange(redirectIndex, 2);
        return (argumentsList, outputFile, false);
      }
      var redirectAppendIndex = argumentsList.IndexOf(">>");
      if (redirectAppendIndex >= 0) {
        var outputFile = argumentsList[redirectAppendIndex + 1];
        argumentsList.RemoveRange(redirectAppendIndex, 2);
        return (argumentsList, outputFile, true);
      }
      return (argumentsList, null, false);
    }
  }
}