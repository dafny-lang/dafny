using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;

namespace XUnitExtensions {
  public interface ILitCommand {
    
    private const string COMMENT_PREFIX = "//";
    private const string LIT_COMMAND_PREFIX = "RUN:";
    private const string LIT_XFAIL = "XFAIL: *";

    public (int, string, string) Execute(TextReader inputReader, TextWriter outputWriter);
    
    public static ILitCommand Parse(string fileName, string line, LitTestConfiguration config) {
      if (!line.StartsWith(COMMENT_PREFIX)) {
        return null;
      }
      line = line[COMMENT_PREFIX.Length..].Trim();

      if (line.Equals(LIT_XFAIL)) {
        return new XFailCommand();
      }
      if (!line.StartsWith(LIT_COMMAND_PREFIX)) {
        return null;
      }
      line = line[LIT_COMMAND_PREFIX.Length..].Trim();
      
      var pieces = ParseArguments(line);
      var commandSymbol = pieces[0];
      var basePath = Path.GetDirectoryName(fileName);
      var (rawArguments, inputFile, outputFile, appendOutput) = ILitCommand.ExtractRedirections(pieces[1..]);
      if (inputFile != null) {
        inputFile = MakeFilePathsAbsolute(basePath, config.ApplySubstitutions(inputFile));
      }
      if (outputFile != null) {
        outputFile = MakeFilePathsAbsolute(basePath, config.ApplySubstitutions(outputFile));
      }
      var arguments = rawArguments
        .Select(config.ApplySubstitutions)
        .Select(arg => MakeFilePathsAbsolute(basePath, arg));
      
      if (config.Commands.TryGetValue(commandSymbol, out var command)) {
        return new LitCommandWithOutput(command(arguments, config), inputFile, outputFile, appendOutput);
      }

      commandSymbol = config.ApplySubstitutions(commandSymbol);

      return new LitCommandWithOutput(
        new ShellLitCommand(commandSymbol, arguments, config.PassthroughEnvironmentVariables), 
        inputFile, outputFile, appendOutput);
    }

    private static string[] ParseArguments(string line) {
      var arguments = new List<string>();
      var argument = new StringBuilder();
      var quoted = false;
      for (int i = 0; i < line.Length; i++) {
        var c = line[i];
        if (c == '"') {
          quoted = !quoted;
        } else if (Char.IsWhiteSpace(c) && !quoted) {
          arguments.Add(argument.ToString());
          argument.Clear();
        } else {
          argument.Append(c);
        }
      }

      if (argument.Length != 0) {
        arguments.Add(argument.ToString());
      }
      
      return arguments.ToArray();
    }
    
    public static string MakeFilePathsAbsolute(string basePath, string s) {
      if (s.StartsWith("-") || s.StartsWith("/")) {
        return s;
      }

      // var absolutePath = Path.Join(basePath, s);
      // if (File.Exists(absolutePath)) {
      //   return absolutePath;
      // }
      
      return s;
    }
    
    public static (IEnumerable<string>, string, string, bool) ExtractRedirections(IEnumerable<string> arguments) {
      var argumentsList = arguments.ToList();
      string inputFile = null;
      string outputFile = null;
      bool appendOutput = false;
      var redirectInIndex = argumentsList.IndexOf("<");
      if (redirectInIndex >= 0) {
        inputFile = argumentsList[redirectInIndex + 1];
        argumentsList.RemoveRange(redirectInIndex, 2);
      }
      var redirectOutIndex = argumentsList.IndexOf(">");
      if (redirectOutIndex >= 0) {
        outputFile = argumentsList[redirectOutIndex + 1];
        argumentsList.RemoveRange(redirectOutIndex, 2);
      }
      var redirectAppendIndex = argumentsList.IndexOf(">>");
      if (redirectAppendIndex >= 0) {
        outputFile = argumentsList[redirectAppendIndex + 1];
        appendOutput = true;
        argumentsList.RemoveRange(redirectAppendIndex, 2);
      }
      return (argumentsList, inputFile, outputFile, appendOutput);
    }
  }
}