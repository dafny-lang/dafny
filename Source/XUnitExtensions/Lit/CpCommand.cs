using System;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions.Lit {
  public class CpCommand : ILitCommand {

    private readonly string options;
    private readonly string fileOrFolder;
    private readonly string destination;

    private CpCommand(string options, string fileOrFolder, string destination) {
      this.options = options;
      this.fileOrFolder = fileOrFolder;
      this.destination = destination;
    }

    public static ILitCommand Parse(string[] args) {
      if (args.Length != 2 && args.Length != 3) {
        throw new ArgumentException($"Wrong number of arguments for cp, expected 2 or 3 but got {args.Length}: " + string.Join(", ", args));
      }

      string fileOrFolder;
      string destination;
      string options;

      if (args.Length == 2) {
        options = "";
        fileOrFolder = args[0];
        destination = args[1];
      } else {
        options = args[0];
        fileOrFolder = args[1];
        destination = args[2];
      }
      return new CpCommand(options, fileOrFolder, destination);
    }
    static void CopyDirectory(string sourceDir, string destinationDir, bool recursive, bool force) {
      // Get information about the source directory
      var dir = new DirectoryInfo(sourceDir);

      // Check if the source directory exists
      if (!dir.Exists) {
        throw new DirectoryNotFoundException($"Source directory not found: {dir.FullName}");
      }

      // Cache directories before we start copying
      DirectoryInfo[] dirs = dir.GetDirectories();

      // Create the destination directory
      Directory.CreateDirectory(destinationDir);

      // Get the files in the source directory and copy to the destination directory
      foreach (FileInfo file in dir.GetFiles()) {
        string targetFilePath = Path.Combine(destinationDir, file.Name);
        if (force && File.Exists(targetFilePath)) {
          File.Delete(targetFilePath);
        }
        file.CopyTo(targetFilePath);
      }

      // If recursive and copying subdirectories, recursively call this method
      if (recursive) {
        foreach (DirectoryInfo subDir in dirs) {
          string newDestinationDir = Path.Combine(destinationDir, subDir.Name);
          CopyDirectory(subDir.FullName, newDestinationDir, true, force);
        }
      }
    }
    public async Task<int> Execute(TextReader inputReader,
      TextWriter outputWriter, TextWriter errorWriter) {
      if (File.Exists(fileOrFolder)) {
        try {
          if (File.Exists(destination) && options.Contains('f')) {
            File.Delete(destination);
          }
          File.Copy(fileOrFolder, destination);
        } catch (Exception e) {
          await outputWriter.WriteLineAsync(e.ToString());
          return 1;
        }
      } else if (Directory.Exists(fileOrFolder)) {
        try {
          var actualDestination = Directory.Exists(destination)
            ? Path.Combine(destination, Path.GetFileName(fileOrFolder))
            : destination;
          CopyDirectory(fileOrFolder, actualDestination, options.Contains('r'), options.Contains('f'));
        } catch (Exception e) {
          await outputWriter.WriteLineAsync(e.ToString());
          return 1;
        }
      } else {
        throw new ArgumentException("File or folder " + fileOrFolder + " not found");
      }

      return 0;
    }

    public override string ToString() {
      return $"%cp {(options != "" ? options + " " : "")}{fileOrFolder} {destination}";
    }
  }
}
