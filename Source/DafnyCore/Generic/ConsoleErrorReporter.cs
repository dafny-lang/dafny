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
    var printMessage = base.MessageCore(source, level, errorId, tok, msg) && (Options is { PrintTooltips: true } || level != ErrorLevel.Info);
    if (!printMessage) {
      return false;
    }

    // Extra indent added to make it easier to distinguish multiline error messages for clients that rely on the CLI
    msg = msg.Replace("\n", "\n ");

    ConsoleColor previousColor = Console.ForegroundColor;
    if (Options.OutputWriter == Console.Out) {
      Console.ForegroundColor = ColorForLevel(level);
    }
    var errorLine = ErrorToString(level, tok, msg);

    if (Options.Verbose && !String.IsNullOrEmpty(errorId) && errorId != "none") {
      errorLine += " (ID: " + errorId + ")\n";
      var info = ErrorRegistry.GetDetail(errorId);
      if (info != null) {
        errorLine += info; // already ends with eol character
      }
    } else {
      errorLine += "\n";
    }

    if (Options.Get(DafnyConsolePrinter.ShowSnippets) && tok.Uri != null) {
      var tw = new StringWriter();
      DafnyConsolePrinter.WriteSourceCodeSnippet(Options, tok.ToRange(), tw);
      errorLine += tw.ToString();
    }

    var innerToken = tok;
    while (innerToken is NestedToken nestedToken) {
      innerToken = nestedToken.Inner;
      if (innerToken.Filepath == nestedToken.Filepath &&
          innerToken.line == nestedToken.line &&
          innerToken.col == nestedToken.col) {
        continue;
      }

      var innerMessage = nestedToken.Message;
      if (innerMessage == null) {
        innerMessage = "Related location";
      } else {
        innerMessage = "Related location: " + innerMessage;
      }

      errorLine += $"{innerToken.TokenToString(Options)}: {innerMessage}\n";
      if (Options.Get(DafnyConsolePrinter.ShowSnippets) && tok.Uri != null) {
        var tw = new StringWriter();
        DafnyConsolePrinter.WriteSourceCodeSnippet(Options, innerToken.ToRange(), tw);
        errorLine += tw.ToString();
      }
    }

    Options.OutputWriter.Write(errorLine);

    if (Options.OutputWriter == Console.Out) {
      Console.ForegroundColor = previousColor;
    }

    return true;
  }

  public ConsoleErrorReporter(DafnyOptions options) : base(options) {
  }
}