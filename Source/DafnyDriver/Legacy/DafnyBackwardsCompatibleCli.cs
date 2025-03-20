using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public interface ILegacyParseArguments { }

// TODO: Refactor so that non-errors (NOT_VERIFIED, DONT_PROCESS_FILES) don't result in non-zero exit codes
public enum ExitValue { SUCCESS = 0, PREPROCESSING_ERROR = 1, DAFNY_ERROR = 2, COMPILE_ERROR = 3, VERIFICATION_ERROR = 4, FORMAT_ERROR = 5 }

public record ParsedOptions(DafnyOptions DafnyOptions) : ILegacyParseArguments;
record ExitImmediately(ExitValue ExitValue) : ILegacyParseArguments;

public static class DafnyBackwardsCompatibleCli {

  public static Task<int> Main(string[] args) {
    return MainWithWriters(Console.Out, Console.Error, Console.In, args);
  }

  static DafnyBackwardsCompatibleCli() {
    // Force all calls to RegisterLegacyUi to be done
    CommonOptionBag.EnsureStaticConstructorHasRun();
    TestCommand.EnsureStaticConstructorHasRun();
  }

  public static Task<int> MainWithWriters(TextWriter outputWriter, TextWriter errorWriter, TextReader inputReader,
    string[] args) {
    // Code that shouldn't be needed, but prevents some exceptions when running the integration tests in parallel
    // outputWriter = new UndisposableTextWriter(outputWriter);
    // errorWriter = new UndisposableTextWriter(errorWriter);
    // outputWriter = TextWriter.Synchronized(outputWriter);
    // errorWriter = TextWriter.Synchronized(errorWriter);

    return Task.Run(() => ThreadMain(outputWriter, errorWriter, inputReader, args));
  }

  private static Task<int> ThreadMain(TextWriter outputWriter, TextWriter errorWriter, TextReader inputReader, string[] args) {
    Contract.Requires(cce.NonNullElements(args));

    var legacyResult = TryLegacyArgumentParser(inputReader, outputWriter, errorWriter, args);
    if (legacyResult == null) {
      var console = new WritersConsole(inputReader, outputWriter, errorWriter);
      return DafnyNewCli.Execute(console, args);
    }

    switch (legacyResult) {
      case ParsedOptions success:
        var options = success.DafnyOptions;
        return SynchronousCliCompilation.Run(options);
      case ExitImmediately failure:
        return Task.FromResult((int)failure.ExitValue);
      default: throw new Exception("unreachable");
    }
  }

  private static ILegacyParseArguments TryLegacyArgumentParser(
    TextReader inputReader,
    TextWriter outputWriter,
    TextWriter errorWriter,
    string[] arguments) {
    if (arguments.Length == 0) {
      return null;
    }
    var dafnyOptions = new DafnyOptions(inputReader, outputWriter, errorWriter) {
      Environment = "Command-line arguments: " + string.Join(" ", arguments)
    };

    var first = arguments[0];
    var keywordForNewMode = DafnyNewCli.RootCommand.Subcommands.Select(c => c.Name).Union(new[]
      { "--version", "-h", DafnyNewCli.ToolchainDebuggingHelpName, "--help", "[parse]", "[suggest]" });
    if (!keywordForNewMode.Contains(first)) {
      if (first.Length > 0 && first[0] != '/' && first[0] != '-' && !File.Exists(first) &&
          first.IndexOf('.') == -1) {
        dafnyOptions.OutputWriter.WriteLine(
          "*** Error: '{0}': The first input must be a command or a legacy option or file with supported extension",
          first);
        return new ExitImmediately(ExitValue.PREPROCESSING_ERROR);
      } else {
        var oldOptions = new DafnyOptions(dafnyOptions.Input, dafnyOptions.OutputWriter, dafnyOptions.ErrorWriter);
        try {
          if (oldOptions.Parse(arguments)) {
            // If requested, print version number, help, attribute help, etc. and exit.
            if (oldOptions.ProcessInfoFlags()) {
              return new ExitImmediately(ExitValue.SUCCESS);
            }

            if (oldOptions.DeprecationNoise != 0) {
              oldOptions.OutputWriter.WriteLine(
                "Warning: this way of using the CLI is deprecated. Use 'dafny --help' to see help for the new Dafny CLI format");
            }

            return new ParsedOptions(oldOptions);
          }

          return new ExitImmediately(ExitValue.PREPROCESSING_ERROR);
        } catch (ProverException pe) {
          new DafnyConsolePrinter(dafnyOptions).ErrorWriteLine(dafnyOptions.OutputWriter,
            "*** ProverException: {0}", pe.Message);
          return new ExitImmediately(ExitValue.PREPROCESSING_ERROR);
        }
      }
    }

    return null;
  }
}