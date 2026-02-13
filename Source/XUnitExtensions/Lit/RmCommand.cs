using System;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions.Lit {
  public class RmCommand : ILitCommand {

    private readonly string options;
    private readonly string fileOrFolder;

    private RmCommand(string options, string fileOrFolder) {
      this.options = options;
      this.fileOrFolder = fileOrFolder;
    }

    public static ILitCommand Parse(string[] args) {
      if (args.Length != 1 && args.Length != 2) {
        throw new ArgumentException($"Wrong number of arguments for rm, expected 1 or 2 but got {args.Length}");
      }

      string fileOrFolder;
      string options;
      if (args.Length == 2) {
        options = args[0];
        fileOrFolder = args[1];
      } else {
        options = "";
        fileOrFolder = args[0];
      }

      return new RmCommand(options, fileOrFolder);
    }
    private static void RecursiveDelete(DirectoryInfo baseDir) {
      if (!baseDir.Exists) {
        return;
      }

      foreach (var dir in baseDir.EnumerateDirectories()) {
        RecursiveDelete(dir);
      }
      baseDir.Delete(true);
    }
    public async Task<int> Execute(TextReader inputReader,
      TextWriter outputWriter, TextWriter errorWriter) {
      if (File.Exists(fileOrFolder)) {
        try {
          File.Delete(fileOrFolder);
        } catch (Exception e) {
          await outputWriter.WriteLineAsync(e.ToString());
          return 1;
        }
      } else if (Directory.Exists(fileOrFolder)) {
        if (Directory.EnumerateFiles(fileOrFolder).Any()) {
          if (options == "-rf") {
            RecursiveDelete(new DirectoryInfo(fileOrFolder));
          } else {
            await outputWriter.WriteLineAsync("Directory is not empty. Please supply rm with -rf to force deletion");
            return 1;
          }
        } else {
          try {
            Directory.Delete(fileOrFolder);
          } catch (Exception e) {
            await outputWriter.WriteLineAsync(e.ToString());
            return 1;
          }
        }
      } else {
        await outputWriter.WriteLineAsync($"File or folder {fileOrFolder} not found");
        return 1;
      }

      return 0;
    }

    public override string ToString() {
      return $"%rm {(options != "" ? options + " " : "")}{fileOrFolder}";
    }
  }
}
