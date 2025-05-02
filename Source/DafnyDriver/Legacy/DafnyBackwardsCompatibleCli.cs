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

    var console = new WritersConsole(inputReader, outputWriter, errorWriter);
    return DafnyNewCli.Execute(console, args);
  }
}