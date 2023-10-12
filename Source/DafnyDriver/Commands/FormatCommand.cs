using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny;

static class FormatCommand {

  public static IEnumerable<Option> Options => DafnyCommands.FormatOptions;

  public static Command Create() {
    var result = new Command("format", @"Format the dafny file in-place.
If no dafny file is provided, will look for every available Dafny file.
Use '--print -' to output the content of the formatted files instead of overwriting them.");
    result.AddArgument(DafnyCommands.FilesArgument);

    foreach (var option in Options) {
      result.AddOption(option);
    }

    DafnyCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, _) => {
      options.AllowSourceFolders = true;
      var exitValue = await DoFormatting(options);
      return (int)exitValue;
    });

    return result;
  }

  public static async Task<ExitValue> DoFormatting(DafnyOptions options) {
    var code = DafnyCli.GetDafnyFiles(options, out var dafnyFiles, out _);
    if (code != 0) {
      return code;
    }
    var errorWriter = options.ErrorWriter;
    var dafnyFileNames = DafnyFile.FileNames(dafnyFiles);
    string programName = dafnyFileNames.Count == 1 ? dafnyFileNames[0] : "the_program";

    var exitValue = ExitValue.SUCCESS;
    Contract.Assert(dafnyFiles.Count > 0 || options.SourceFolders.Count > 0);
    dafnyFiles = dafnyFiles.Concat(options.SourceFolders.SelectMany(folderPath => {
      return Directory.GetFiles(folderPath, "*.dfy", SearchOption.AllDirectories)
          .Select(name => new DafnyFile(options, new Uri(name))).ToList();
    })).ToList();

    var failedToParseFiles = new List<string>();
    var emptyFiles = new List<string>();
    var doCheck = options.FormatCheck;
    var doPrint = options.DafnyPrintFile == "-";
    options.DafnyPrintFile = null;
    var neededFormatting = 0;
    foreach (var file in dafnyFiles) {
      var dafnyFile = file;
      if (!dafnyFile.Uri.IsFile && !doCheck && !doPrint) {
        await errorWriter.WriteLineAsync("Please use the '--check' and/or '--print' option as stdin cannot be formatted in place.");
        exitValue = ExitValue.PREPROCESSING_ERROR;
        continue;
      }

      string tempFileName = null;
      if (!dafnyFile.Uri.IsFile) {
        tempFileName = Path.GetTempFileName() + ".dfy";
        CompilerDriver.WriteFile(tempFileName, await Console.In.ReadToEndAsync());
        dafnyFile = new DafnyFile(options, new Uri(tempFileName));
      }

      using var content = dafnyFile.GetContent();
      var originalText = await content.ReadToEndAsync();
      dafnyFile.GetContent = () => new StringReader(originalText);
      // Might not be totally optimized but let's do that for now
      var err = DafnyMain.Parse(new List<DafnyFile> { dafnyFile }, programName, options, out var dafnyProgram);
      if (err != null) {
        exitValue = ExitValue.DAFNY_ERROR;
        await errorWriter.WriteLineAsync(err);
        failedToParseFiles.Add(dafnyFile.BaseName);
      } else {
        var firstToken = dafnyProgram.GetFirstTokenForUri(file.Uri);
        var result = originalText;
        if (firstToken != null) {
          result = Formatting.__default.ReindentProgramFromFirstToken(firstToken,
            IndentationFormatter.ForProgram(dafnyProgram));
          if (result != originalText) {
            neededFormatting += 1;
            if (doCheck) {
              exitValue = exitValue != ExitValue.DAFNY_ERROR ? ExitValue.FORMAT_ERROR : exitValue;
            }

            if (doCheck && (!doPrint || options.Verbose)) {
              await options.OutputWriter.WriteLineAsync("The file " +
                                                        (options.UseBaseNameForFileName
                                                          ? Path.GetFileName(dafnyFile.FilePath)
                                                          : dafnyFile.FilePath) + " needs to be formatted");
            }

            if (!doCheck && !doPrint) {
              CompilerDriver.WriteFile(dafnyFile.FilePath, result);
            }
          }
        } else {
          // TODO: is this necessary? there already is a warning about files containing no code
          if (options.Verbose) {
            await options.ErrorWriter.WriteLineAsync(dafnyFile.BaseName + " was empty.");
          }

          emptyFiles.Add((options.UseBaseNameForFileName
            ? Path.GetFileName(dafnyFile.FilePath)
            : dafnyFile.FilePath));
        }
        if (doPrint) {
          await options.OutputWriter.WriteAsync(result);
        }
      }

      if (tempFileName != null) {
        File.Delete(tempFileName);
      }
    }

    string Files(int num) {
      return num + (num != 1 ? " files" : " file");
    }

    // Report any errors
    var reportMsg = "";
    if (failedToParseFiles.Count > 0) {
      reportMsg += $"\n{Files(failedToParseFiles.Count)} failed to parse:\n  " + string.Join("\n  ", failedToParseFiles);
    }
    if (emptyFiles.Count > 0) {
      reportMsg += $"\n{Files(emptyFiles.Count)} {(emptyFiles.Count > 1 ? "were" : "was")} empty:\n  " + string.Join("\n  ", emptyFiles);
    }

    var unchanged = dafnyFiles.Count - failedToParseFiles.Count - emptyFiles.Count - neededFormatting;
    reportMsg += unchanged > 0 && (failedToParseFiles.Count > 0 || emptyFiles.Count > 0) ? $"\n{Files(unchanged)} {(unchanged > 1 ? "were" : "was")} already formatted." : "";
    var filesNeedFormatting = neededFormatting == 0 ? "" : $"{Files(neededFormatting)} need{(neededFormatting > 1 ? "" : "s")} formatting.";
    reportMsg = filesNeedFormatting + reportMsg;

    if (doCheck) {
      await options.OutputWriter.WriteLineAsync(neededFormatting > 0
        ? $"Error: {reportMsg}"
        : "All files are correctly formatted");
    } else if (failedToParseFiles.Count > 0 || options.Verbose) {
      // We don't display anything if we just format files without verbosity and there was no parse error
      await options.OutputWriter.WriteLineAsync($"{reportMsg}");
    }

    return exitValue;
  }
}
