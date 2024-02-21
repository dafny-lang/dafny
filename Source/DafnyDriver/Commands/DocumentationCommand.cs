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
    CompilerErrors.RunStaticConstructor();
    ResolutionErrors.RunStaticConstructor();
  }
  public static Command Create() {
    var result = new Command("documentation", "Generates someDafny documentation files for errors based on a template");
    result.IsHidden = true;

    result.AddArgument(FileInfoArgument);
    result.SetHandler(CreateDocumentation);

    return result;
  }

  private static void CreateDocumentation(InvocationContext context)
  {
    var file = context.ParseResult.GetValueForArgument(FileInfoArgument);
      
    var outputPath = file.FullName.Replace("template","tmp");
    using var reader = file.OpenRead();
    var textReader = new StreamReader(reader);
    using var writer = File.OpenWrite(outputPath);
    var textWriter = new StreamWriter(writer);
    string errorId = null;
    int number = 0;
    while (textReader.ReadLine() is { } line) {
      number++;
      if (line.StartsWith("## **")) {
        int k = line.IndexOf("{#", StringComparison.Ordinal);
        int kk = line.LastIndexOf("}", StringComparison.Ordinal);
        if (k == -1 || kk == -1) {
          Console.WriteLine("SYNTAX ERROR IN TEMPLATE LINE " + number + ": no errorid");
          context.ExitCode = 1;
          return;
        }
        errorId = line.Substring(k+2, kk - (k+2));
        textWriter.WriteLine(line);
        continue;
      }
      if (line.Contains("INSERT-TEXT")) {
        var text = ErrorRegistry.GetDetail(errorId);
        if (text != null) {
          textWriter.Write(text); // text already has trailing newline
        } else {
          textWriter.WriteLine(line);
          Console.Out.WriteLine("Unknown errorid: " + errorId);
        }
      } else {
        textWriter.WriteLine(line);
      }
    }
  }
}