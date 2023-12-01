using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public static class VerifyCommand {

  public static Command Create() {
    var result = new Command("verify", "Verify the program.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }
    DafnyCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => {
      if (options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
        options.TrackVerificationCoverage = true;
      }
      options.Compile = false;
      return CompilerDriver.RunCompiler(options);
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