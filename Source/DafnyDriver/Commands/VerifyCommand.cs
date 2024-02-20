using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using System.Threading.Tasks;
using DafnyCore;
using DafnyDriver.Commands;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public static class VerifyCommand {

  static VerifyCommand() {
    DooFile.RegisterNoChecksNeeded(FilterSymbol);
    DooFile.RegisterNoChecksNeeded(FilterPosition);
  }

  public static readonly Option<string> FilterSymbol = new("--filter-symbol",
    @"Filter what gets verified by selecting only symbols whose fully qualified name contains the given argument. For example: ""--filter-symbol=MyNestedModule.MyFooFunction""");

  public static readonly Option<string> FilterPosition = new("--filter-position",
    @"Filter what gets verified based on a source location. The location is specified as a file path suffix, optionally followed by a colon and a line number. For example: ""--filter-position=lastFolder/source.dfy:23""");

  public static Command Create() {
    var result = new Command("verify", "Verify the program.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, _) => {
      if (options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
        options.TrackVerificationCoverage = true;
      }


      
      if (options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
        // --log-format and --verification-coverage-report are not yet supported by CliCompilation
        options.Compile = false;
        return await SynchronousCliCompilation.Run(options);
      }
      
      ProofDependencyManager depManager = new();
      var compilation = CliCompilation.Create(options);
      compilation.Start();
      var verificationResults = await compilation.VerifyAllAndPrintSummary();
      
      if (options.VerificationLoggerConfigs.Any()) {
        try {
          VerificationResultLogger.RaiseTestLoggerEvents(options, verificationResults, depManager);
        } catch (ArgumentException ae) {
          options.Printer.ErrorWriteLine(options.OutputWriter, $"*** Error: {ae.Message}");
          return (int)ExitValue.PREPROCESSING_ERROR;
        }
      }
      
      return compilation.ExitCode;
    });
    return result;
  }

  private static IReadOnlyList<Option> Options =>
    new Option[] {
        FilterSymbol,
        FilterPosition,
        BoogieOptionBag.BoogieFilter,
      }.Concat(DafnyCommands.VerificationOptions).
      Concat(DafnyCommands.ConsoleOutputOptions).
      Concat(DafnyCommands.ResolverOptions);
}
