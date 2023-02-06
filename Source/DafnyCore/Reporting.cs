// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using static Microsoft.Dafny.ErrorDetail;

namespace Microsoft.Dafny {
  public enum ErrorLevel {
    Info, Warning, Error
  }

  public enum MessageSource {
    Parser, Cloner, RefinementTransformer, Rewriter, Resolver, Translator, Verifier, Compiler
  }

  public struct ErrorMessage {
    public ErrorID errorID;
    public IToken token;
    public string message;
    public MessageSource source;
  }

  public abstract class ErrorReporter {
    public bool ErrorsOnly { get; set; }

    public bool HasErrors => ErrorCount > 0;
    public int ErrorCount => Count(ErrorLevel.Error);
    public bool HasErrorsUntilResolver => ErrorCountUntilResolver > 0;
    public int ErrorCountUntilResolver => CountExceptVerifierAndCompiler(ErrorLevel.Error);


    public abstract bool Message(MessageSource source, ErrorLevel level, ErrorID errorID, IToken tok, string msg);

    public void Error(MessageSource source, IToken tok, string msg) {
      Error(source, ErrorID.None, tok, msg);
    }
    public void Error(MessageSource source, ErrorID errorID, IToken tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      // if the tok is IncludeToken, we need to indicate to the including file
      // that there are errors in the included file.
      if (tok is IncludeToken) {
        IncludeToken includeToken = (IncludeToken)tok;
        Include include = includeToken.Include;
        if (!include.ErrorReported) {
          Message(source, ErrorLevel.Error, ErrorID.None, include.tok, "the included file " + tok.Filename + " contains error(s)");
          include.ErrorReported = true;
        }
      }
      Message(source, ErrorLevel.Error, errorID, tok, msg);
    }

    public abstract int Count(ErrorLevel level);
    public abstract int CountExceptVerifierAndCompiler(ErrorLevel level);

    // This method required by the Parser
    internal void Error(MessageSource source, ErrorID errorID, string filename, int line, int col, string msg) {
      var tok = new Token(line, col);
      tok.Filename = filename;
      Error(source, errorID, tok, msg);
    }

    public void Error(MessageSource source, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, ErrorID.None, tok, String.Format(msg, args));
    }

    public void Error(MessageSource source, ErrorID errorID, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, errorID, tok, String.Format(msg, args));
    }

    public void Error(MessageSource source, Declaration d, string msg, params object[] args) {
      Contract.Requires(d != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, ErrorID.None, d.tok, msg, args);
    }

    public void Error(MessageSource source, ErrorID errorID, Declaration d, string msg, params object[] args) {
      Contract.Requires(d != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, errorID, d.tok, msg, args);
    }

    public void Error(MessageSource source, Statement s, string msg, params object[] args) {
      Contract.Requires(s != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, ErrorID.None, s.Tok, msg, args);
    }

    public void Error(MessageSource source, IVariable v, string msg, params object[] args) {
      Contract.Requires(v != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, ErrorID.None, v.Tok, msg, args);
    }

    public void Error(MessageSource source, Expression e, string msg, params object[] args) {
      Contract.Requires(e != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, ErrorID.None, e.tok, msg, args);
    }

    public void Warning(MessageSource source, ErrorID errorID, IToken tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      if (DafnyOptions.O.WarningsAsErrors) {
        Error(source, errorID, tok, msg);
      } else {
        Message(source, ErrorLevel.Warning, errorID, tok, msg);
      }
    }

    public void Warning(MessageSource source, ErrorID errorID, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Warning(source, errorID, tok, String.Format(msg, args));
    }

    public void Deprecated(MessageSource source, ErrorID errorID, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      if (DafnyOptions.O.DeprecationNoise != 0) {
        Warning(source, errorID, tok, String.Format(msg, args));
      }
    }

    public void DeprecatedStyle(MessageSource source, ErrorID errorID, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      if (DafnyOptions.O.DeprecationNoise == 2) {
        Warning(source, errorID, tok, String.Format(msg, args));
      }
    }


    public void Info(MessageSource source, IToken tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Message(source, ErrorLevel.Info, ErrorID.None, tok, msg);
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
      return String.Format("{0}({1},{2})", tok.Filename, tok.line, tok.col - 1);
    }
  }

  public abstract class BatchErrorReporter : ErrorReporter {
    protected readonly Dictionary<ErrorLevel, List<ErrorMessage>> AllMessages;

    protected BatchErrorReporter() {
      ErrorsOnly = false;
      AllMessages = new Dictionary<ErrorLevel, List<ErrorMessage>> {
        [ErrorLevel.Error] = new(),
        [ErrorLevel.Warning] = new(),
        [ErrorLevel.Info] = new()
      };
    }

    public override bool Message(MessageSource source, ErrorLevel level, ErrorID errorID, IToken tok, string msg) {
      if (ErrorsOnly && level != ErrorLevel.Error) {
        // discard the message
        return false;
      }
      AllMessages[level].Add(new ErrorMessage { errorID = errorID, token = tok, message = msg, source = source });
      return true;
    }

    public override int Count(ErrorLevel level) {
      return AllMessages[level].Count;
    }

    public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
      return AllMessages[level].Count(message => message.source != MessageSource.Verifier &&
                                                 message.source != MessageSource.Compiler);
    }
  }

  public class ConsoleErrorReporter : BatchErrorReporter {
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

    public override bool Message(MessageSource source, ErrorLevel level, ErrorID errorID, IToken tok, string msg) {
      if (base.Message(source, level, errorID, tok, msg) && (DafnyOptions.O is { PrintTooltips: true } || level != ErrorLevel.Info)) {
        // Extra indent added to make it easier to distinguish multiline error messages for clients that rely on the CLI
        msg = msg.Replace("\n", "\n ");

        ConsoleColor previousColor = Console.ForegroundColor;
        Console.ForegroundColor = ColorForLevel(level);
        var errorLine = ErrorToString(level, tok, msg);
        while (tok is NestedToken nestedToken) {
          tok = nestedToken.Inner;
          if (tok.Filename == nestedToken.Filename &&
              tok.line == nestedToken.line &&
              tok.col == nestedToken.col) {
            continue;
          }
          msg = nestedToken.Message ?? "[Related location]";
          errorLine += $" {msg} {TokenToString(tok)}";
        }

        if (DafnyOptions.O.CompileVerbose && false) { // Need to control tests better before we enable this
          var info = ErrorDetail.GetDetail(errorID);
          if (info != null) {
            errorLine += "\n" + info;
          }
        }
        Console.WriteLine(errorLine);

        Console.ForegroundColor = previousColor;
        return true;
      } else {
        return false;
      }
    }
  }

  public class ErrorReporterSink : ErrorReporter {
    public ErrorReporterSink() { }

    public override bool Message(MessageSource source, ErrorLevel level, ErrorID errorID, IToken tok, string msg) {
      return false;
    }

    public override int Count(ErrorLevel level) {
      return 0;
    }

    public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
      return 0;
    }
  }

  public class ErrorReporterWrapper : BatchErrorReporter {

    private string msgPrefix;
    public readonly ErrorReporter WrappedReporter;

    public ErrorReporterWrapper(ErrorReporter reporter, string msgPrefix) {
      this.msgPrefix = msgPrefix;
      this.WrappedReporter = reporter;
    }

    public override bool Message(MessageSource source, ErrorLevel level, ErrorID errorID, IToken tok, string msg) {
      base.Message(source, level, errorID, tok, msg);
      return WrappedReporter.Message(source, level, errorID, tok, msgPrefix + msg);
    }
  }
}
