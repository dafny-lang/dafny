using System;
using System.IO;
using DafnyCore;

namespace Microsoft.Dafny;

public class ConsoleErrorReporter(DafnyOptions options) : BatchErrorReporter(options) {
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

  public override bool MessageCore(DafnyDiagnostic dafnyDiagnostic) {
    var printMessage = base.MessageCore(dafnyDiagnostic) && (Options is { PrintTooltips: true } || dafnyDiagnostic.Level != ErrorLevel.Info);

    if (!printMessage) {
      return false;
    }

    // Extra indent added to make it easier to distinguish multiline error messages for clients that rely on the CLI
    var msg = dafnyDiagnostic.Message.Replace("\n", "\n ");

    ConsoleColor previousColor = Console.ForegroundColor;
    if (Options.OutputWriter == Console.Out) {
      Console.ForegroundColor = ColorForLevel(dafnyDiagnostic.Level);
    }

    var errorLine = ErrorToString(dafnyDiagnostic.Level, dafnyDiagnostic.Location, msg);

    var errorId = dafnyDiagnostic.ErrorId;
    if (Options.Verbose && !String.IsNullOrEmpty(errorId) && errorId != "none") {
      errorLine += " (ID: " + errorId + ")\n";
      var info = ErrorRegistry.GetDetail(errorId);
      if (info != null) {
        errorLine += info; // already ends with eol character
      }
    } else {
      errorLine += "\n";
    }

    if (Options.Get(Snippets.ShowSnippets) && dafnyDiagnostic.Location != null) {
      var tw = new StringWriter();
      Snippets.WriteSourceCodeSnippet(Options, dafnyDiagnostic.Location, tw);
      errorLine += tw.ToString();
    }

    foreach (var related in dafnyDiagnostic.RelatedInformation) {
      var innerMessage = related.Message;
      if (string.IsNullOrEmpty(innerMessage)) {
        innerMessage = "Related location";
      }

      errorLine += $"{related.Location.LocationToString(Options)}: {innerMessage}\n";
      if (Options.Get(Snippets.ShowSnippets)) {
        var tw = new StringWriter();
        Snippets.WriteSourceCodeSnippet(Options, related.Location, tw);
        errorLine += tw.ToString();
      }
    }

    Options.OutputWriter.Write(errorLine);

    if (Options.OutputWriter == Console.Out) {
      Console.ForegroundColor = previousColor;
    }

    return true;
  }
}