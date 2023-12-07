using System;
using System.IO;

namespace Microsoft.Dafny;

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

      if (Options.Get(DafnyConsolePrinter.ShowSnippets) && tok.Uri != null) {
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