using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using Microsoft.Extensions.FileSystemGlobbing;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public interface ILitCommand {

    private static readonly Dictionary<string, Func<string, LitTestConfiguration, ILitCommand>> CommandParsers = new();
    static ILitCommand() {
      CommandParsers.Add("RUN:", RunCommand.Parse);
      CommandParsers.Add("UNSUPPORTED:", UnsupportedCommand.Parse);
      CommandParsers.Add("XFAIL:", XFailCommand.Parse);
    }

    public static ILitCommand? Parse(string line, LitTestConfiguration config) {
      foreach (var (keyword, parser) in CommandParsers) {
        var index = line.IndexOf(keyword);
        if (index >= 0) {
          var arguments = line[(index + keyword.Length)..].Trim();
          return parser(arguments, config);
        }
      }
      return null;
    }

    public static string[] Tokenize(string line) {
      var arguments = new List<string>();
      var argument = new StringBuilder();
      var singleQuoted = false;
      var doubleQuoted = false;
      var hasGlobCharacters = false;
      for (int i = 0; i < line.Length; i++) {
        var c = line[i];
        if (c == '\'' && !doubleQuoted) {
          singleQuoted = !singleQuoted;
        } else if (c == '"' && !singleQuoted) {
          doubleQuoted = !doubleQuoted;
        } else if (Char.IsWhiteSpace(c) && !(singleQuoted || doubleQuoted)) {
          if (argument.Length != 0) {
            if (hasGlobCharacters) {
              arguments.AddRange(ExpandGlobs(argument.ToString()));
            } else {
              arguments.Add(argument.ToString());
            }

            argument.Clear();
            hasGlobCharacters = false;
          }
        } else {
          if (c is '*' or '?' && !singleQuoted) {
            hasGlobCharacters = true;
          }
          argument.Append(c);
        }
      }

      if (argument.Length != 0) {
        if (hasGlobCharacters) {
          arguments.AddRange(ExpandGlobs(argument.ToString()));
        } else {
          arguments.Add(argument.ToString());
        }
      }

      return arguments.ToArray();
    }

    protected static IEnumerable<string> ExpandGlobs(string chunk) {
      var matcher = new Matcher();
      matcher.AddInclude(chunk);
      var result = matcher.Execute(new DirectoryInfoWrapper(new DirectoryInfo(".")));
      return result.Files.Select(f => f.Path);
    }

    public (int, string, string) Execute(ITestOutputHelper? outputHelper, TextReader? inputReader, TextWriter? outputWriter, TextWriter? errorWriter);
  }
}
