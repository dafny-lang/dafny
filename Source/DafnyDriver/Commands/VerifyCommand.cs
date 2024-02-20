using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using System.Threading.Tasks;
using DafnyCore;
using DafnyDriver.Commands;

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
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, _) => await HandleVerification(options));
    return result;
  }

  public static async Task<int> HandleVerification(DafnyOptions options) {
    if (options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
      options.TrackVerificationCoverage = true;
    }

    var compilation = CliCompilation.Create(options);
    compilation.Start();
    var verificationResults = await compilation.VerifyAllAndPrintSummary();

    if (verificationResults != null) {
      var resolution = await compilation.Resolution;
      var proofDependencyManager = resolution.ResolvedProgram.ProofDependencyManager;
      if (options.VerificationLoggerConfigs.Any()) {
        try {
          VerificationResultLogger.RaiseTestLoggerEvents(options, verificationResults, proofDependencyManager);
        } catch (ArgumentException ae) {
          options.Printer.ErrorWriteLine(options.OutputWriter, $"*** Error: {ae.Message}");
          return (int)ExitValue.PREPROCESSING_ERROR;
        }
      }

      var coverageReportDir = options.Get(CommonOptionBag.VerificationCoverageReport);
      if (coverageReportDir != null) {
        new CoverageReporter(options).SerializeVerificationCoverageReport(
          proofDependencyManager, resolution.ResolvedProgram,
          verificationResults.Values.
            SelectMany(v => v.CompletedParts).
            SelectMany(v => v.Result.Result.CoveredElements).ToHashSet(),
          coverageReportDir);
      }
    }

    return compilation.ExitCode;
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
