using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using Microsoft.Dafny;

namespace DafnyDriver.Commands;

public class DocumentationCommand {
  
  public static Command Create() {
    var result = new Command("documentation", "Generates some Dafny documentation files based on a template");
    result.IsHidden = true;
    
    var fileInfoArgument = new Argument<FileInfo>();
    result.AddArgument(fileInfoArgument);
    result.SetHandler(context => {
      var file = context.ParseResult.GetValueForArgument(fileInfoArgument);
      
      var outname = file.FullName.Replace("template","tmp");
      using var reader = file.OpenRead();
      var textReader = new StreamReader(reader);
      using var writer = File.OpenWrite(outname);
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
          errorId = line.Substring(k+2, kk);
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
    });

    return result;
  }
}