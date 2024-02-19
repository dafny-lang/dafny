using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny;

public static class DafnyCommands {

  public static Argument<FileInfo> FileArgument { get; }
  public static Argument<List<FileInfo>> FilesArgument { get; }

  static DafnyCommands() {

    FileArgument = new Argument<FileInfo>("file", "Dafny input file or Dafny project file");
    FilesArgument = new("file", r => {
      return r.Tokens.Where(t => !string.IsNullOrEmpty(t.Value)).Select(t => new FileInfo(t.Value)).ToList();
    }, false, "Dafny input files and/or a Dafny project file");
  }

  public static IEnumerable<Option> FormatOptions => new Option[] {
    CommonOptionBag.Check,
    CommonOptionBag.FormatPrint,
  }.Concat(ParserOptions);

  public static IReadOnlyList<Option> VerificationOptions = new Option[] {
    CommonOptionBag.RelaxDefiniteAssignment,
    BoogieOptionBag.VerificationTimeLimit,
    CommonOptionBag.VerifyIncludedFiles,
    CommonOptionBag.ManualLemmaInduction,
    BoogieOptionBag.SolverPath,
    CommonOptionBag.DisableNonLinearArithmetic,
    BoogieOptionBag.IsolateAssertions,
    BoogieOptionBag.BoogieArguments,
    CommonOptionBag.VerificationLogFormat,
    BoogieOptionBag.SolverResourceLimit,
    BoogieOptionBag.SolverOption,
    BoogieOptionBag.SolverOptionHelp,
    BoogieOptionBag.SolverPlugin,
    BoogieOptionBag.SolverLog,
    CommonOptionBag.JsonDiagnostics,
    BoogieOptionBag.VerificationErrorLimit,
    CommonOptionBag.DefaultFunctionOpacity,
    CommonOptionBag.WarnContradictoryAssumptions,
    CommonOptionBag.WarnRedundantAssumptions,
    CommonOptionBag.NoTimeStampForCoverageReport,
    CommonOptionBag.VerificationCoverageReport,
    CommonOptionBag.ExtractCounterexample,
    CommonOptionBag.ShowInference,
    CommonOptionBag.ManualTriggerOption
  }.ToList();

  public static IReadOnlyList<Option> TranslationOptions = new Option[] {
    BoogieOptionBag.NoVerify,
    CommonOptionBag.EnforceDeterminism,
    CommonOptionBag.OptimizeErasableDatatypeWrapper,
    CommonOptionBag.TestAssumptions,
    DeveloperOptionBag.Bootstrapping,
    CommonOptionBag.AddCompileSuffix,
    CommonOptionBag.SystemModule
  }.Concat(VerificationOptions).ToList();

  public static readonly IReadOnlyList<Option> ExecutionOptions = new Option[] {
    CommonOptionBag.Target,
    CommonOptionBag.SpillTranslation,
    CommonOptionBag.InternalIncludeRuntimeOptionForExecution,
    CommonOptionBag.ExecutionCoverageReport
  }.Concat(TranslationOptions).ToList();

  public static readonly IReadOnlyList<Option> ConsoleOutputOptions = new List<Option>(new Option[] {
    DafnyConsolePrinter.ShowSnippets,
    DeveloperOptionBag.PrintOption,
    DeveloperOptionBag.ResolvedPrint,
    DeveloperOptionBag.BoogiePrint,
    Printer.PrintMode,
    CommonOptionBag.AllowWarnings,
  });

  public static readonly IReadOnlyList<Option> ParserOptions = new List<Option>(new Option[] {
    CommonOptionBag.StdIn,
    CommonOptionBag.Verbose,
    BoogieOptionBag.Cores,
    CommonOptionBag.Libraries,
    CommonOptionBag.AllowDeprecation,
    CommonOptionBag.PluginOption,
    CommonOptionBag.Prelude,
    Function.FunctionSyntaxOption,
    CommonOptionBag.QuantifierSyntax,
    CommonOptionBag.UnicodeCharacters,
    CommonOptionBag.UseBaseFileName,
    CommonOptionBag.GeneralTraits,
    CommonOptionBag.GeneralNewtypes,
    CommonOptionBag.TypeSystemRefresh,
    CommonOptionBag.TypeInferenceDebug,
    CommonOptionBag.NewTypeInferenceDebug,
    CommonOptionBag.ReadsClausesOnMethods,
    CommonOptionBag.UseStandardLibraries,
    CommonOptionBag.LogLevelOption,
    CommonOptionBag.LogLocation
  });

  public static IReadOnlyList<Option> ResolverOptions = new List<Option>(new Option[] {
    CommonOptionBag.WarnShadowing,
    CommonOptionBag.WarnMissingConstructorParenthesis,
    PrintStmt.TrackPrintEffectsOption,
  }).Concat(ParserOptions).ToList();
}