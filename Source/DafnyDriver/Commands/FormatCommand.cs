using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny;

class FormatCommand : ICommandSpec {

  public static readonly Option<bool> Check = new("--check", () => false, @"
Instead of formatting files, verify that all files are already
formatted through and return a non-zero exit code if it is not the case".TrimStart());

  public IEnumerable<Option> Options => new Option[] {
      Check,
      CommonOptionBag.Plugin,
      DeveloperOptionBag.UseBaseFileName,
      DeveloperOptionBag.Print,
      BoogieOptionBag.BoogieFilter,
    }.
    Concat(ICommandSpec.ConsoleOutputOptions).
    Concat(ICommandSpec.CommonOptions);

  static FormatCommand() {
    DafnyOptions.RegisterLegacyBinding(Check, (options, value) => {
      options.FormatCheck = value;
    });
  }

  public Command Create() {
    var result = new Command("format", @"Format the dafny file in-place.
If no dafny file is provided, will look for every available Dafny file.
Use '--print -' to output the content of the formatted files instead of overwriting them.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Format = true;
    dafnyOptions.Compile = false;
  }

  public static DafnyDriver.ExitValue DoFormatting(IList<DafnyFile> dafnyFiles, ErrorReporter reporter, string programName) {
    var exitValue = DafnyDriver.ExitValue.SUCCESS;
    if (dafnyFiles.Count == 0) {
      // Let's list all the dafny files recursively in the working directory
      dafnyFiles = Directory.GetFiles(Directory.GetCurrentDirectory(), "*.dfy", SearchOption.AllDirectories)
        .Select(name => new DafnyFile(name)).ToList();
    }

    var failed = new List<string>();
    var onlyCheck = DafnyOptions.O.FormatCheck;
    var onlyPrint = DafnyOptions.O.DafnyPrintFile == "-";
    DafnyOptions.O.DafnyPrintFile = null;
    var needFormatting = 0;
    foreach (var dafnyFile in dafnyFiles) {
      if (dafnyFile.UseStdin && !onlyCheck) {
        continue;
      }

      // Might not be totally optimized but let's do that for now
      var err = Main.Parse(new List<DafnyFile> { dafnyFile }, programName, reporter, out var dafnyProgram);
      string originalText = File.ReadAllText(dafnyFile.FilePath);
      if (err != null) {
        exitValue = DafnyDriver.ExitValue.DAFNY_ERROR;
        Console.Error.WriteLine(err);
        failed.Add(dafnyFile.BaseName);
      } else {
        var firstToken = dafnyProgram.GetFirstTopLevelToken();
        if (firstToken != null) {
          var result = Formatting.__default.ReindentProgramFromFirstToken(firstToken,
            IndentationFormatter.ForProgram(dafnyProgram));
          if (onlyPrint) {
            Console.Out.Write(result);
          } else if (onlyCheck) {
            if (result != originalText) {
              Console.Out.WriteLine("The file " + dafnyFile.FilePath + " needs to be formatted");
              exitValue = DafnyDriver.ExitValue.DAFNY_ERROR;
              needFormatting += 1;
            }
          } else {
            DafnyDriver.WriteFile(dafnyFile.FilePath, result);
          }
        } else {
          Console.Error.WriteLine(dafnyFile.BaseName + " was empty.");
          failed.Add(dafnyFile.BaseName);
        }
      }
    }

    var unchanged = dafnyFiles.Count - failed.Count - needFormatting;
    var unchangedMessage = unchanged > 0 ? $" {Files(unchanged)} were already formatted." : "";

    string Files(int num) {
      return num + (num != 1 ? " files" : " file");
    }

    var errorMsg = failed.Count > 0
      ? $" {Files(failed.Count)} failed to parse or were empty:\n" + string.Join("\n", failed)
      : "";
    if (!onlyCheck && (dafnyFiles.Count != 1 || failed.Count > 0)) {
      Console.Out.WriteLine($"{Files(needFormatting)} formatted." + unchangedMessage + errorMsg);
    }

    if (onlyCheck) {
      Console.Out.WriteLine(needFormatting > 0
        ? $"Error: {Files(needFormatting)} need formatting." + unchangedMessage + errorMsg
        : "All files correctly formatted");
    }

    return exitValue;
  }
}
