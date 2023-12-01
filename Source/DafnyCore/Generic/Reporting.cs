// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny {
  public enum ErrorLevel {
    Info, Warning, Error
  }

  public enum MessageSource {
    Project, Parser, Cloner, RefinementTransformer, Rewriter, Resolver, Translator, Verifier, Compiler, Documentation, TestGeneration
  }

  public record DafnyRelatedInformation(IToken Token, string Message);
  public record DafnyDiagnostic(string ErrorId, IToken Token, string Message,
    MessageSource Source, ErrorLevel Level,
    IReadOnlyList<DafnyRelatedInformation> RelatedInformation);

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

    protected override bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg) {
      if (base.MessageCore(source, level, errorId, tok, msg) && (Options is { PrintTooltips: true } || level != ErrorLevel.Info)) {
        // Extra indent added to make it easier to distinguish multiline error messages for clients that rely on the CLI
        msg = msg.Replace("\n", "\n ");

        ConsoleColor previousColor = Console.ForegroundColor;
        if (Options.OutputWriter == Console.Out) {
          Console.ForegroundColor = ColorForLevel(level);
        }
        var errorLine = ErrorToString(level, tok, msg);
        while (tok is NestedToken nestedToken) {
          tok = nestedToken.Inner;
          if (tok.Filepath == nestedToken.Filepath &&
              tok.line == nestedToken.line &&
              tok.col == nestedToken.col) {
            continue;
          }
          msg = nestedToken.Message ?? "[Related location]";
          errorLine += $" {msg} {tok.TokenToString(Options)}";
        }

        if (Options.Verbose && !String.IsNullOrEmpty(errorId) && errorId != "none") {
          errorLine += " (ID: " + errorId + ")\n";
          var info = ErrorRegistry.GetDetail(errorId);
          if (info != null) {
            errorLine += info; // already ends with eol character
          }
        } else {
          errorLine += "\n";
        }

        Options.OutputWriter.Write(errorLine);

        if (Options.Get(DafnyConsolePrinter.ShowSnippets) && tok != Token.NoToken) {
          TextWriter tw = new StringWriter();
          new DafnyConsolePrinter(Options).WriteSourceCodeSnippet(tok.ToRange(), tw);
          Options.OutputWriter.Write(tw.ToString());
        }

        if (Options.OutputWriter == Console.Out) {
          Console.ForegroundColor = previousColor;
        }
        return true;
      }

      return false;
    }

    public ConsoleErrorReporter(DafnyOptions options) : base(options) {
    }
  }

  public class ErrorReporterSink : ErrorReporter {
    public ErrorReporterSink(DafnyOptions options) : base(options) { }

    protected override bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg) {
      return false;
    }

    public override void Error(MessageSource source, string errorId, IToken tok, string msg) {

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

    protected override bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg) {
      base.MessageCore(source, level, errorId, tok, msg);
      return WrappedReporter.Message(source, level, errorId, tok, msgPrefix + msg);
    }
  }
}
