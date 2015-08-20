using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny {
  public enum ErrorLevel {
    Info, Warning, Error
  }

  public enum MessageSource {
    Parser, Resolver, Translator, Rewriter, Other,
    RefinementTransformer,
    Cloner
  }

  public struct ErrorMessage {
    public IToken token;
    public string message;
    public MessageSource source;
  }

  public abstract class ErrorReporter {
    public bool ErrorsOnly { get; set; }
    public Dictionary<ErrorLevel, List<ErrorMessage>> AllMessages { get; private set; }

    protected ErrorReporter() {
      ErrorsOnly = false;
      AllMessages = new Dictionary<ErrorLevel, List<ErrorMessage>>();
      AllMessages[ErrorLevel.Error] = new List<ErrorMessage>();
      AllMessages[ErrorLevel.Warning] = new List<ErrorMessage>();
      AllMessages[ErrorLevel.Info] = new List<ErrorMessage>();
    }

    // This is the only thing that needs to be overriden
    public virtual bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
      bool discard = (ErrorsOnly && level != ErrorLevel.Error) || // Discard non-errors if ErrorsOnly is set
                     (tok is TokenWrapper && !(tok is NestedToken)); // Discard wrapped tokens, except for nested ones
      if (!discard) {
        AllMessages[level].Add(new ErrorMessage { token = tok, message = msg });
      }
      return !discard;
    }

    public int Count(ErrorLevel level) {
      return AllMessages[level].Count;
    }

    public void Error(MessageSource source, IToken tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Message(source, ErrorLevel.Error, tok, msg);
    }

    // This method required by the Parser
    internal void Error(MessageSource source, string filename, int line, int col, string msg) {
      var tok = new Token(line, col);
      tok.filename = filename;
      Error(source, tok, msg);
    }

    public void Error(MessageSource source, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Error(source, tok, String.Format(msg, args));
    }

    public void Error(MessageSource source, Declaration d, string msg, params object[] args) {
      Contract.Requires(d != null);
      Contract.Requires(msg != null);
      Error(source, d.tok, msg, args);
    }

    public void Error(MessageSource source, Statement s, string msg, params object[] args) {
      Contract.Requires(s != null);
      Contract.Requires(msg != null);
      Error(source, s.Tok, msg, args);
    }

    public void Error(MessageSource source, NonglobalVariable v, string msg, params object[] args) {
      Contract.Requires(v != null);
      Contract.Requires(msg != null);
      Error(source, v.tok, msg, args);
    }

    public void Error(MessageSource source, Expression e, string msg, params object[] args) {
      Contract.Requires(e != null);
      Contract.Requires(msg != null);
      Error(source, e.tok, msg, args);
    }

    public void Warning(MessageSource source, IToken tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Message(source, ErrorLevel.Warning, tok, msg);
    }

    public void Warning(MessageSource source, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Warning(source, tok, String.Format(msg, args));
    }

    public void Info(MessageSource source, IToken tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Message(source, ErrorLevel.Info, tok, msg);
    }

    public void Info(MessageSource source, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Info(source, tok, String.Format(msg, args));
    }

    public static string ErrorToString(ErrorLevel header, IToken tok, string msg) {
      return ErrorToString_Internal(": " + header.ToString(), tok.filename, tok.line, tok.col, ": " + msg);
    }

    public static string ErrorToString(ErrorLevel header, string filename, int oneBasedLine, int oneBasedColumn, string msg) {
      return ErrorToString_Internal(": " + header.ToString(), filename, oneBasedLine, oneBasedColumn, ": " + msg);
    }

    public static string ErrorToString_Internal(string header, string filename, int oneBasedLine, int oneBasedColumn, string msg) {
      return String.Format("{0}({1},{2}){3}{4}", filename, oneBasedLine, oneBasedColumn - 1, header, msg ?? "");
    }
  }

  public class ConsoleErrorReporter : ErrorReporter {
    private ConsoleColor ColorForLevel(ErrorLevel level) {
      switch (level) {
        case ErrorLevel.Error:
          return ConsoleColor.Red;
        case ErrorLevel.Warning:
          return ConsoleColor.Yellow;
        case ErrorLevel.Info:
          return ConsoleColor.Green;
        default:
          throw new cce.UnreachableException();
      }
    }

    public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
      if (base.Message(source, level, tok, msg) && (DafnyOptions.O.PrintTooltips || level != ErrorLevel.Info)) {
        // Extra indent added to make it easier to distinguish multiline error messages for clients that rely on the CLI
        msg = msg.Replace(Environment.NewLine, Environment.NewLine + " ");

        ConsoleColor previousColor = Console.ForegroundColor;
        Console.ForegroundColor = ColorForLevel(level);
        Console.WriteLine(ErrorToString(level, tok, msg));
        Console.ForegroundColor = previousColor;
        return true;
      } else {
        return false;
      }
    }
  }
}
