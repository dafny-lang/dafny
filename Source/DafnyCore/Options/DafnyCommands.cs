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
    CommonOptionBag.VerificationCoverageReport
  }.ToList();

  public static IReadOnlyList<Option> TranslationOptions = new Option[] {
    BoogieOptionBag.NoVerify,
    CommonOptionBag.EnforceDeterminism,
    CommonOptionBag.OptimizeErasableDatatypeWrapper,
    CommonOptionBag.TestAssumptions,
    DeveloperOptionBag.Bootstrapping,
    CommonOptionBag.AddCompileSuffix,
  }.Concat(VerificationOptions).ToList();

  public static IReadOnlyList<Option> ExecutionOptions = new Option[] {
    CommonOptionBag.Target,
    CommonOptionBag.SpillTranslation
  }.Concat(TranslationOptions).ToList();

  public static IReadOnlyList<Option> ConsoleOutputOptions = new List<Option>(new Option[] {
    DafnyConsolePrinter.ShowSnippets,
    DeveloperOptionBag.Print,
    DeveloperOptionBag.ResolvedPrint,
    DeveloperOptionBag.BoogiePrint,
    Printer.PrintMode,
    CommonOptionBag.WarningAsErrors,
  });

  public static IReadOnlyList<Option> ParserOptions = new List<Option>(new Option[] {
    CommonOptionBag.StdIn,
    CommonOptionBag.Verbose,
    BoogieOptionBag.Cores,
    CommonOptionBag.Libraries,
    CommonOptionBag.WarnDeprecation,
    CommonOptionBag.PluginOption,
    CommonOptionBag.Prelude,
    Function.FunctionSyntaxOption,
    CommonOptionBag.QuantifierSyntax,
    CommonOptionBag.UnicodeCharacters,
    CommonOptionBag.UseBaseFileName,
    CommonOptionBag.GeneralTraits,
    CommonOptionBag.TypeSystemRefresh,
    CommonOptionBag.TypeInferenceDebug,
    CommonOptionBag.NewTypeInferenceDebug,
    CommonOptionBag.ReadsClausesOnMethods
  });

  public static IReadOnlyList<Option> ResolverOptions = new List<Option>(new Option[] {
    CommonOptionBag.WarnShadowing,
    CommonOptionBag.WarnMissingConstructorParenthesis,
    PrintStmt.TrackPrintEffectsOption,
  }).Concat(ParserOptions).ToList();
}