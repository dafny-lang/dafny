using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using System.Threading.Tasks;
using DafnyDriver.Commands;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public static class VerifyCommand {

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
      var compilation = CliCompilation.Create(options);
      compilation.Start();
      await compilation.VerifyAllAndPrintSummary();
      return compilation.ExitCode;
    });
    return result;
  }

  private static IReadOnlyList<Option> Options =>
    new Option[] {
        BoogieOptionBag.BoogieFilter,
      }.Concat(DafnyCommands.VerificationOptions).
      Concat(DafnyCommands.ConsoleOutputOptions).
      Concat(DafnyCommands.ResolverOptions);
}
