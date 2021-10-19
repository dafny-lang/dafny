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

namespace XUnitExtensions.Lit {
  public interface ILitCommand {

    private static readonly Dictionary<string, Type> CommandClasses = new();
    static ILitCommand() {
      CommandClasses.Add("RUN:", typeof(RunCommand));
      CommandClasses.Add("UNSUPPORTED:", typeof(UnsupportedCommand));
      CommandClasses.Add("XFAIL:", typeof(XFailCommand));
    }
    
    public static ILitCommand? Parse(string line, LitTestConfiguration config) {
      foreach (var (keyword, type) in CommandClasses) {
        var index = line.IndexOf(keyword);
        if (index >= 0) {
          var arguments = line[(index + keyword.Length)..].Trim();
          var parseMethod = type.GetMethod("Parse", new[] { typeof(string), typeof(LitTestConfiguration) });
          return (ILitCommand)parseMethod!.Invoke(null, new object[] { arguments, config });
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
        if (c == '\'') {
          singleQuoted = !singleQuoted;
        } else if (c == '"') {
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
    
    protected static IEnumerable<string> ExpandGlobs(string chunk ) {
      var matcher = new Matcher();
      matcher.AddInclude(chunk);
      var result = matcher.Execute(new DirectoryInfoWrapper(new DirectoryInfo(".")));
      return result.Files.Select(f => f.Path);
    }
    
    public (int, string, string) Execute(ITestOutputHelper outputHelper, TextReader? inputReader, TextWriter? outputWriter, TextWriter? errorWriter);
  }
}