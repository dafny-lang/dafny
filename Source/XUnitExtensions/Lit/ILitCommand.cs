using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.AccessControl;
using System.Text;
using Microsoft.Extensions.FileSystemGlobbing;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {

  public record Token(string Value, Kind Kind);

  public enum Kind { Verbatim, MustGlob }

  public class DelayedLitCommand : ILitCommand {
    public Func<ILitCommand> Factory { get; }
    public ILitCommand? command;

    public DelayedLitCommand(Func<ILitCommand> factory) {
      this.Factory = factory;
    }

    public (int, string, string) Execute(TextReader inputReader,
      TextWriter outputWriter,
      TextWriter errorWriter) {
      if (command == null) {
        command = Factory();
      }
      return command.Execute(inputReader, outputWriter, errorWriter);
    }

    public override string? ToString() {
      if (command == null) {
        command = Factory();
      }
      return command!.ToString();
    }
  }
  public interface ILitCommand {

    private static readonly Dictionary<string, Func<string, LitTestConfiguration, ILitCommand>> CommandParsers = new();
    static ILitCommand() {
      CommandParsers.Add("RUN:", RunCommand.Parse);
      CommandParsers.Add("UNSUPPORTED:", UnsupportedCommand.Parse);
      CommandParsers.Add("XFAIL:", XFailCommand.Parse);
      CommandParsers.Add("NONUNIFORM:", NonUniformTestCommand.Parse);
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

    public static Token[] Tokenize(string line) {
      var result = new List<Token>();
      var inProgressArgument = new StringBuilder();
      var singleQuoted = false;
      var doubleQuoted = false;
      var kind = Kind.Verbatim;
      var tokenStarted = false;
      foreach (var c in line) {
        if (c == '\'' && !doubleQuoted) {
          singleQuoted = !singleQuoted;
          tokenStarted = true;
        } else if (c == '"' && !singleQuoted) {
          doubleQuoted = !doubleQuoted;
          tokenStarted = true;
        } else if (Char.IsWhiteSpace(c) && !(singleQuoted || doubleQuoted)) {
          if (tokenStarted) {
            result.Add(new Token(inProgressArgument.ToString(), kind));
            inProgressArgument.Clear();
            kind = Kind.Verbatim;
            tokenStarted = false;
          }
        } else {
          if (c is '?' && inProgressArgument.Length == 1 && inProgressArgument[0] == '-') {
            kind = Kind.Verbatim;
          } else if (c is '*' or '?' && !singleQuoted) {
            kind = Kind.MustGlob;
          }
          inProgressArgument.Append(c);
          tokenStarted = true;
        }
      }

      if (tokenStarted) {
        result.Add(new Token(inProgressArgument.ToString(), kind));
      }

      return result.ToArray();
    }

    public (int, string, string) Execute(TextReader inputReader, TextWriter outputWriter, TextWriter errorWriter);
  }
}
