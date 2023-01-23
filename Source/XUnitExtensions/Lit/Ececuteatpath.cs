using System;
using System.IO;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions.Lit {
  /// <summary>
  /// This class implements the equivalent of the Unix 'diff' command that lit tests rely on,
  /// because 'diff' does not exist on Windows.
  /// </summary>
  public class Executeatpath : ILitCommand {

    private readonly string executionpath;


    private Executeatpath(string executionpath) {
      this.executionpath = executionpath;
    }

    public static ILitCommand Parse(string[] args) {
      if (args.Length != 1) {
        throw new ArgumentException($"Wrong number of arguments for executeatpath: {args}");
      }

      var executionpath = args[0];
      return new Executeatpath(executionpath);
    }

    public (int, string, string) Execute(ITestOutputHelper? outputHelper, TextReader? inputReader,
      TextWriter? outputWriter, TextWriter? errorWriter) {
      Directory.SetCurrentDirectory(executionpath);
      return (0, "", "");
    }
  }
}