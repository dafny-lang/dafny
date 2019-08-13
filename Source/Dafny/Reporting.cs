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
    Cloner,
    Compiler
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
                     (tok is TokenWrapper && !(tok is IncludeToken) && !(tok is NestedToken) && !(tok is RefinementToken)); // Discard wrapped tokens, except for included, nested and refinement
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
      // if the tok is IncludeToken, we need to indicate to the including file
      // that there are errors in the included file.
      if (tok is IncludeToken) {
        IncludeToken includeToken = (IncludeToken) tok;
        Include include = includeToken.Include;
        if (!include.ErrorReported) {
          Message(source, ErrorLevel.Error, include.tok, "the included file " + tok.filename + " contains error(s)");
          include.ErrorReported = true;
        }
      }
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
      Contract.Requires(args != null);
      Error(source, tok, String.Format(msg, args));
    }

    public void Error(MessageSource source, Declaration d, string msg, params object[] args) {
      Contract.Requires(d != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, d.tok, msg, args);
    }

    public void Error(MessageSource source, Statement s, string msg, params object[] args) {
      Contract.Requires(s != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, s.Tok, msg, args);
    }

    public void Error(MessageSource source, IVariable v, string msg, params object[] args) {
      Contract.Requires(v != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, v.Tok, msg, args);
    }

    public void Error(MessageSource source, Expression e, string msg, params object[] args) {
      Contract.Requires(e != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, e.tok, msg, args);
    }

    public void Warning(MessageSource source, IToken tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Message(source, ErrorLevel.Warning, tok, msg);
    }

    public void Deprecated(MessageSource source, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      if (DafnyOptions.O.DeprecationNoise != 0) {
        Warning(source, tok, String.Format(msg, args));
      }
    }
    public void DeprecatedStyle(MessageSource source, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      if (DafnyOptions.O.DeprecationNoise == 2) {
        Warning(source, tok, String.Format(msg, args));
      }
    }

    public void Warning(MessageSource source, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
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
      Contract.Requires(args != null);
      Info(source, tok, String.Format(msg, args));
    }

    public static string ErrorToString(ErrorLevel header, IToken tok, string msg) {
      return String.Format("{0}: {1}{2}", TokenToString(tok), header.ToString(), ": " + msg);
    }

    public static string TokenToString(IToken tok) {
      return String.Format("{0}({1},{2})", tok.filename, tok.line, tok.col - 1);
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
      if (base.Message(source, level, tok, msg) && ((DafnyOptions.O != null && DafnyOptions.O.PrintTooltips) || level != ErrorLevel.Info)) {
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

  public class ErrorReporterSink : ErrorReporter {
    public ErrorReporterSink() {}

    public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
      return false;
    }
  }

  public class ErrorReporterWrapper : ErrorReporter {

    private string msgPrefix;
    public readonly ErrorReporter WrappedReporter;

    public ErrorReporterWrapper(ErrorReporter reporter, string msgPrefix) {
      this.msgPrefix = msgPrefix;
      this.WrappedReporter = reporter;
    }

    public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
      base.Message(source, level, tok, msg);
      return WrappedReporter.Message(source, level, tok, msgPrefix + msg);
    }
  }
}
