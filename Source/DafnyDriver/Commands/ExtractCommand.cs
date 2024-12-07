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
    result.AddArgument(SourceModule);
    result.AddArgument(Target);
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in ExtractOptions) {
      result.AddOption(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => HandleExtraction(options));
    return result;
  }

  private static readonly Argument<string> SourceModule = new("The name of the module to be extracted.");

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

    var sourceModuleName = options.Get(SourceModule);
    var outputPath = options.Get(Target).FullName;
    using var engine = ExecutionEngine.CreateWithoutSharedCache(options);
    try {
      var extractedProgram = BoogieExtractor.Extract(resolution.ResolvedProgram, sourceModuleName);
      engine.PrintBplFile(outputPath, extractedProgram, true, pretty: true);
    } catch (ExtractorError extractorError) {
      var tok = extractorError.Tok;
      await options.OutputWriter.WriteLineAsync($"{tok.filename}({tok.line},{tok.col}): Boogie axiom extraction error: {extractorError.Message}");
      return 1;
    }

    return await compilation.GetAndReportExitCode();
  }
}
