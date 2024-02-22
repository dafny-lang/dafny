using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.IO;
using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;

namespace DafnyDriver.Commands;

public class DocumentationCommand {
  private static readonly Argument<FileInfo> FileInfoArgument = new();

  static DocumentationCommand() {
    GeneratorErrors.RunStaticConstructor();
    ResolutionErrors.RunStaticConstructor();
    ParseErrors.RunStaticConstructor();
  }
  public static Command Create() {
    var result = new Command("documentation", "Generates some Dafny documentation files for errors based on a template");
    result.IsHidden = true;

    result.AddArgument(FileInfoArgument);
    result.SetHandler(CreateDocumentation);

    return result;
  }

  private static void CreateDocumentation(InvocationContext context) {
    var file = context.ParseResult.GetValueForArgument(FileInfoArgument);

    var outputPath = file.FullName.Replace("template", "tmp");
    using var reader = file.OpenRead();
    var textReader = new StreamReader(reader);
    using var textWriter = new StreamWriter(outputPath);
    string errorId = null;
    int lineNumber = 0;
    while (textReader.ReadLine() is { } line) {
      lineNumber++;
      if (line.StartsWith("## **")) {
        int errorIdStart = line.IndexOf("{#", StringComparison.Ordinal);
        int errorIdEnd = line.LastIndexOf("}", StringComparison.Ordinal);
        if (errorIdStart == -1 || errorIdEnd == -1) {
          Console.WriteLine("SYNTAX ERROR IN TEMPLATE LINE " + lineNumber + ": no errorid");
          context.ExitCode = 1;
          return;
        }
        errorId = line.Substring(errorIdStart + 2, errorIdEnd - (errorIdStart + 2));
        textWriter.WriteLine(line);
        continue;
      }
      if (line.Contains("INSERT-TEXT")) {
        var text = ErrorRegistry.GetDetail(errorId);
        if (text != null) {
          textWriter.Write(text); // text already has trailing newline
        } else {
          textWriter.WriteLine(line);
          Console.Out.WriteLine("Unknown errorId: " + errorId);
        }
      } else {
        textWriter.WriteLine(line);
      }
    }
    textWriter.Flush();
  }
}