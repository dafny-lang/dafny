using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;

namespace XUnitExtensions {
  public interface ILitCommand {
    
    private const string COMMENT_PREFIX = "//";
    private const string LIT_COMMAND_PREFIX = "RUN:";

    public (int, string, string) Execute(TextWriter outputWriter);
    
    public static LitCommandWithOutput Parse(string fileName, string line, LitTestConfiguration config) {
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
      var basePath = Path.GetDirectoryName(fileName);
      var (rawArguments, outputFile, appendOutput) = ILitCommand.ExtractOutputFile(pieces[1..]);
      if (outputFile != null) {
        outputFile = MakeFilePathsAbsolute(basePath, config.ApplySubstitutions(outputFile));
      }
      var arguments = rawArguments
        .Select(config.ApplySubstitutions)
        .Select(arg => MakeFilePathsAbsolute(basePath, arg));
      
      if (config.Commands.TryGetValue(commandSymbol, out var command)) {
        return new LitCommandWithOutput(command(arguments, config), outputFile, appendOutput);
      }

      commandSymbol = config.ApplySubstitutions(commandSymbol);

      return new LitCommandWithOutput(new ShellLitCommand(commandSymbol, arguments, config.PassthroughEnvironmentVariables), outputFile, appendOutput);
    }

    private static string StripQuotes(string s) {
      if (s.Length >= 2 && s[0] == '"' && s[^1] == '"') {
        return s[1..^1];
      }
      return s;
    }

    public static string MakeFilePathsAbsolute(string basePath, string s) {
      if (s.StartsWith("-") || s.StartsWith("/")) {
        return s;
      }
      return Path.Join(basePath, s);
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