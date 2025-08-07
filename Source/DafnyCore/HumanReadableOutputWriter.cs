using System;
using System.IO;
using System.Threading.Tasks;
using DafnyCore;

namespace Microsoft.Dafny;

public class HumanReadableOutputWriter(DafnyOptions options) : IDafnyOutputWriter {

  public void Debug(string message) {
    if (string.IsNullOrEmpty(message)) {
      return;
    }
    options.BaseOutputWriter.WriteLine(message);
  }

  public void Exception(string message) {
    options.BaseOutputWriter.WriteLine(message);
  }

  public Task Status(string message) {
    return options.BaseOutputWriter.WriteLineAsync(message);
  }

  public Task Code(string message) {
    return options.BaseOutputWriter.WriteAsync(message);
  }

  public TextWriter StatusWriter() {
    return new StringWriterWithDispose(s => options.BaseOutputWriter.Write(s));
  }

  public TextWriter ErrorWriter() {
    return new StringWriterWithDispose(s => options.ErrorWriter.Write(s));
  }

  public void WriteDiagnostic(DafnyDiagnostic diagnostic) {
    ConsoleColor previousColor = Console.ForegroundColor;
    if (options.BaseOutputWriter == Console.Out) {
      Console.ForegroundColor = ColorForLevel(diagnostic.Level);
    }

    // Extra indent added to make it easier to distinguish multiline error messages for clients that rely on the CLI
    var errorLine = ErrorReporter.FormatDiagnostic(options, diagnostic).Replace("\n", "\n ");

    if (options.Verbose && !String.IsNullOrEmpty(diagnostic.ErrorId) && diagnostic.ErrorId != "none") {
      errorLine += " (ID: " + diagnostic.ErrorId + ")\n";
      var info = ErrorRegistry.GetDetail(diagnostic.ErrorId);
      if (info != null) {
        errorLine += info; // already ends with eol character
      }
    } else {
      errorLine += "\n";
    }

    if (options.Get(Snippets.ShowSnippets) && diagnostic.Range.Uri != null) {
      var tw = new StringWriter();
      Snippets.WriteSourceCodeSnippet(options, diagnostic.Range, tw);
      errorLine += tw.ToString();
    }

    foreach (var related in diagnostic.RelatedInformation) {
      var innerMessage = related.Message;
      if (string.IsNullOrEmpty(innerMessage)) {
        innerMessage = "Related location";
      } else {
        innerMessage = "Related location: " + innerMessage;
      }

      errorLine += $"{related.Range.ToFileRangeString(options)}: {innerMessage}\n";
      if (options.Get(Snippets.ShowSnippets)) {
        var tw = new StringWriter();
        Snippets.WriteSourceCodeSnippet(options, related.Range, tw);
        errorLine += tw.ToString();
      }
    }

    options.BaseOutputWriter.Write(errorLine);

    if (options.BaseOutputWriter == Console.Out) {
      Console.ForegroundColor = previousColor;
    }
  }

  public Task Error(string message) {
    throw new NotImplementedException();
  }

  private ConsoleColor ColorForLevel(ErrorLevel level) {
    switch (level) {
      case ErrorLevel.Error:
        return ConsoleColor.Red;
      case ErrorLevel.Warning:
        return ConsoleColor.Yellow;
      case ErrorLevel.Info:
        return ConsoleColor.Green;
      default:
        throw new Cce.UnreachableException();
    }
  }
}

class StringWriterWithDispose(Action<string> onDispose) : StringWriter {
  protected override void Dispose(bool disposing) {
    onDispose(ToString());
    base.Dispose(disposing);
  }
}