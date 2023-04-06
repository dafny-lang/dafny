// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  public enum ErrorLevel {
    Info, Warning, Error
  }

  public enum MessageSource {
    Parser, Cloner, RefinementTransformer, Rewriter, Resolver, Translator, Verifier, Compiler, Documentation
  }

  public record DafnyRelatedInformation(IToken Token, string Message);
  public record DafnyDiagnostic(string ErrorId, IToken Token, string Message,
    MessageSource Source, ErrorLevel Level,
    IReadOnlyList<DafnyRelatedInformation> RelatedInformation);

  public abstract class ErrorReporter {
    public DafnyOptions Options { get; }

    protected ErrorReporter(DafnyOptions options) {
      this.Options = options;
    }

    public bool ErrorsOnly { get; set; }

    public bool HasErrors => ErrorCount > 0;
    public int ErrorCount => Count(ErrorLevel.Error);
    public bool HasErrorsUntilResolver => ErrorCountUntilResolver > 0;
    public int ErrorCountUntilResolver => CountExceptVerifierAndCompiler(ErrorLevel.Error);

    public abstract bool Message(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg);

    public void Error(MessageSource source, IToken tok, string msg) {
      Error(source, null, tok, msg);
    }
    public void Error(MessageSource source, string errorId, IToken tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      // if the tok is IncludeToken, we need to indicate to the including file
      // that there are errors in the included file.
      if (tok is IncludeToken) {
        IncludeToken includeToken = (IncludeToken)tok;
        Include include = includeToken.Include;
        if (!include.ErrorReported) {
          Message(source, ErrorLevel.Error, null, include.tok, "the included file " + tok.Filename + " contains error(s)");
          include.ErrorReported = true;
        }
      }
      Message(source, ErrorLevel.Error, errorId, tok, msg);
    }

    public abstract int Count(ErrorLevel level);
    public abstract int CountExceptVerifierAndCompiler(ErrorLevel level);

    // This method required by the Parser
    internal void Error(MessageSource source, string errorId, string filename, int line, int col, string msg) {
      var tok = new Token(line, col);
      tok.Filename = filename;
      Error(source, errorId, tok, msg);
    }

    public void Error(MessageSource source, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, null, tok, String.Format(msg, args));
    }

    public void Error(MessageSource source, string errorId, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, errorId, tok, String.Format(msg, args));
    }

    public void Error(MessageSource source, Declaration d, string msg, params object[] args) {
      Contract.Requires(d != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, null, d.tok, msg, args);
    }

    public void Error(MessageSource source, string errorId, Declaration d, string msg, params object[] args) {
      Contract.Requires(d != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, errorId, d.tok, msg, args);
    }

    public void Error(MessageSource source, Statement s, string msg, params object[] args) {
      Contract.Requires(s != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, null, s.Tok, msg, args);
    }

    public void Error(MessageSource source, INode v, string msg, params object[] args) {
      Contract.Requires(v != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, null, v.Tok, msg, args);
    }

    public void Error(MessageSource source, Expression e, string msg, params object[] args) {
      Contract.Requires(e != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Error(source, null, e.tok, msg, args);
    }

    public void Warning(MessageSource source, string errorId, IToken tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      if (Options.WarningsAsErrors) {
        Error(source, errorId, tok, msg);
      } else {
        Message(source, ErrorLevel.Warning, errorId, tok, msg);
      }
    }

    public void Warning(MessageSource source, string errorId, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      Warning(source, errorId, tok, String.Format(msg, args));
    }

    public void Deprecated(MessageSource source, string errorId, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      if (Options.DeprecationNoise != 0) {
        Warning(source, errorId, tok, String.Format(msg, args));
      }
    }

    public void DeprecatedStyle(MessageSource source, string errorId, IToken tok, string msg, params object[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(args != null);
      if (Options.DeprecationNoise == 2) {
        Warning(source, errorId, tok, String.Format(msg, args));
      }
    }


    public void Info(MessageSource source, IToken tok, string msg) {
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Message(source, ErrorLevel.Info, null, tok, msg);
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

    public override bool Message(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg) {
      if (base.Message(source, level, errorId, tok, msg) && (Options is { PrintTooltips: true } || level != ErrorLevel.Info)) {
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

        if (Options.CompileVerbose && false) { // Need to control tests better before we enable this
          var info = ErrorRegistry.GetDetail(errorId);
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

    public ConsoleErrorReporter(DafnyOptions options) : base(options) {
    }
  }

  public class ErrorReporterSink : ErrorReporter {
    public ErrorReporterSink(DafnyOptions options) : base(options) { }

    public override bool Message(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg) {
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

    public ErrorReporterWrapper(ErrorReporter reporter, string msgPrefix) : base(reporter.Options) {
      this.msgPrefix = msgPrefix;
      this.WrappedReporter = reporter;
    }

    public override bool Message(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg) {
      base.Message(source, level, errorId, tok, msg);
      return WrappedReporter.Message(source, level, errorId, tok, msgPrefix + msg);
    }
  }
}
