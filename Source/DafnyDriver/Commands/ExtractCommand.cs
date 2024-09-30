#nullable enable
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Threading.Tasks;
using DafnyDriver.Commands;
using Microsoft.Boogie;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny;

public static class ExtractCommand {
  public static Command Create() {

    var result = new Command("extract", "Can be used to generate DafnyPrelude.bpl. Uses the ':extract_boogie_name' attribute to rename symbols. Turns lemmas into universally quantified axioms, as opposed to verify which turns them into Boogie procedures. When translating Dafny expressions to Boogie ones, no well-formedness checks are created.");

    result.IsHidden = true;
    result.AddArgument(Target);
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in ExtractOptions) {
      result.AddOption(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => HandleExtraction(options));
    return result;
  }

  private static readonly Argument<FileInfo> Target = new("The path of the extracted file.");

  private static IReadOnlyList<Option> ExtractOptions =>
    new Option[] { }.
      Concat(DafnyCommands.ConsoleOutputOptions).
      Concat(DafnyCommands.ResolverOptions);

  public static async Task<int> HandleExtraction(DafnyOptions options) {
    if (options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
      options.TrackVerificationCoverage = true;
    }

    var compilation = CliCompilation.Create(options);
    compilation.Start();

    var resolution = await compilation.Resolution;
    if (resolution is not { HasErrors: false }) {
      return await compilation.GetAndReportExitCode();
    }

    var outputPath = options.Get(Target).FullName;
    using var engine = ExecutionEngine.CreateWithoutSharedCache(options);
    try {
      var extractedProgram = BoogieExtractor.Extract(resolution.ResolvedProgram);
      engine.PrintBplFile(outputPath, extractedProgram, true, pretty: true);
    } catch (ExtractorError extractorError) {
      await options.OutputWriter.WriteLineAsync($"Boogie axiom extraction error: {extractorError.Message}");
      return 1;
    }

    return await compilation.GetAndReportExitCode();
  }
}
