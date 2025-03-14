using System;
using System.IO;
using DafnyCore;

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

  public override bool MessageCore(DafnyDiagnostic diagnostic) {
    var printMessage = base.MessageCore(diagnostic) && (Options is { PrintTooltips: true } || diagnostic.Level != ErrorLevel.Info);
    if (!printMessage) {
      return false;
    }

    // Extra indent added to make it easier to distinguish multiline error messages for clients that rely on the CLI
    var msg = diagnostic.Message.Replace("\n", "\n ");

    ConsoleColor previousColor = Console.ForegroundColor;
    if (Options.OutputWriter == Console.Out) {
      Console.ForegroundColor = ColorForLevel(diagnostic.Level);
    }
    var errorLine = ErrorToString(diagnostic.Level, diagnostic.Range, msg);

    if (Options.Verbose && !String.IsNullOrEmpty(diagnostic.ErrorId) && diagnostic.ErrorId != "none") {
      errorLine += " (ID: " + diagnostic.ErrorId + ")\n";
      var info = ErrorRegistry.GetDetail(diagnostic.ErrorId);
      if (info != null) {
        errorLine += info; // already ends with eol character
      }
    } else {
      errorLine += "\n";
    }

    if (Options.Get(Snippets.ShowSnippets) && diagnostic.Range.Uri != null) {
      var tw = new StringWriter();
      Snippets.WriteSourceCodeSnippet(Options, diagnostic.Range.EntireRange, tw);
      errorLine += tw.ToString();
    }

    foreach (var related in diagnostic.RelatedInformation) {
      var innerMessage = related.Message;
      if (string.IsNullOrEmpty(innerMessage)) {
        innerMessage = "Related location";
      } else {
        innerMessage = "Related location: " + innerMessage;
      }

      errorLine += $"{related.Token.OriginToString(Options)}: {innerMessage}\n";
      if (Options.Get(Snippets.ShowSnippets)) {
        var tw = new StringWriter();
        Snippets.WriteSourceCodeSnippet(Options, related.Token.EntireRange, tw);
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