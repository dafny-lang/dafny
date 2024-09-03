using System;
using System.IO;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions.Lit {
  public class MvCommand : ILitCommand {

    private readonly string fileOrFolder;
    private readonly string destination;

    private MvCommand(string fileOrFolder, string destination) {
      this.fileOrFolder = fileOrFolder;
      this.destination = destination;
    }

    public static ILitCommand Parse(string[] args) {
      if (args.Length != 2) {
        throw new ArgumentException($"Wrong number of arguments for mv, expected 2 but got {args.Length}");
      }
      var fileOrFolder = args[0];
      var destination = args[1];

      return new MvCommand(fileOrFolder, destination);
    }

    public async Task<int> Execute(TextReader inputReader,
      TextWriter outputWriter, TextWriter errorWriter) {
      if (File.Exists(fileOrFolder)) {
        try {
          File.Move(fileOrFolder, destination);
        } catch (Exception e) {
          await outputWriter.WriteLineAsync(e.ToString());
          return 1;
        }
      } else if (Directory.Exists(fileOrFolder)) {
        try {
          Directory.Move(fileOrFolder, destination);
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
      return $"%mv {fileOrFolder} {destination}";
    }
  }
}
