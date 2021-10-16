using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using Microsoft.Extensions.FileSystemGlobbing;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Xunit;
using Xunit.Abstractions;

namespace XUnitExtensions {
  public interface ILitCommand {

    private const string COMMENT_PREFIX = "//";
    private const string LIT_COMMAND_PREFIX = "RUN:";
    private const string LIT_XFAIL = "XFAIL: *";

    public (int, string, string) Execute(ITestOutputHelper outputHelper, TextReader inputReader, TextWriter outputWriter, TextWriter errorWriter);

    public void ExecuteWithExpectation(ITestOutputHelper outputHelper, TextReader inputReader, TextWriter outputWriter, TextWriter errorWriter, bool expectFailure = false) {
      try {
        outputHelper.WriteLine($"Executing command: {this}");
        var (exitCode, output, error) = Execute(outputHelper, inputReader, outputWriter, errorWriter);
        
        if (expectFailure) {
          if (exitCode != 0) {
            throw new SkipException($"Command returned non-zero exit code ({exitCode}): {this}\nOutput:\n{output}\nError:\n{error}");
          }
        }

        if (exitCode != 0) {
          throw new Exception($"Command returned non-zero exit code ({exitCode}): {this}\nOutput:\n{output}\nError:\n{error}");
        }
      } catch (Exception e) {
        throw new Exception($"Exception thrown while executing command: {this}", e);
      }
    }
    
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

      var tokens = Tokenize(line);
      return ParseRunCommand(tokens, config);
    }

    public static ILitCommand ParseRunCommand(string[] tokens, LitTestConfiguration config) {
      // Just supporting || for now since it's a precise way to ignore an exit code
      var seqOperatorIndex = Array.IndexOf(tokens, "||");
      if (seqOperatorIndex >= 0) {
        var lhs = LitCommandWithRedirection.Parse(tokens[0..seqOperatorIndex], config);
        var rhs = ParseRunCommand(tokens[(seqOperatorIndex + 1)..], config);
        return new OrCommand(lhs, rhs);
      }
      return LitCommandWithRedirection.Parse(tokens, config);
    }

    private static string[] Tokenize(string line) {
      var arguments = new List<string>();
      var argument = new StringBuilder();
      var singleQuoted = false;
      var doubleQuoted = false;
      for (int i = 0; i < line.Length; i++) {
        var c = line[i];
        if (c == '\'') {
          singleQuoted = !singleQuoted;
          argument.Append(c);
        } else if (c == '"') {
          doubleQuoted = !doubleQuoted;
        } else if (Char.IsWhiteSpace(c) && !(singleQuoted || doubleQuoted)) {
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
    
    protected static IEnumerable<string> ExpandGlobsAndBackticks(string chunk, LitTestConfiguration config, ITestOutputHelper outputHelper) {
      if (chunk.Contains('*') || chunk.Contains('?')) {
        var matcher = new Matcher();
        matcher.AddInclude(chunk);
        var result = matcher.Execute(new DirectoryInfoWrapper(new DirectoryInfo(".")));
        return result.Files.Select(f => f.Path);
      }

      var firstTickIndex = chunk.IndexOf('`');
      if (firstTickIndex >= 0) {
        var secondTickIndex = chunk.IndexOf('`', firstTickIndex + 1);
        var toParse = chunk[(firstTickIndex + 1)..(secondTickIndex)];
        ILitCommand command = LitCommandWithRedirection.Parse(Tokenize(toParse), config);
        var output = new StringBuilder();
        command.ExecuteWithExpectation(outputHelper, null, new StringWriter(output), null);
        return new[] { chunk[..firstTickIndex] + output + chunk[(secondTickIndex + 1)..] };
      }
      return new[] { chunk };
    }
  }
}