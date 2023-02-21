using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.CommandLine.Parsing;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny;

public interface ICommandSpec {

  public static Argument<FileInfo> FileArgument { get; }

  static ICommandSpec() {
    FilesArgument = new Argument<IEnumerable<FileInfo>>("file", "input files");
  }
  public static Argument<IEnumerable<FileInfo>> FilesArgument { get; }

  public static IEnumerable<Option> FormatOptions => new Option[] {
    CommonOptionBag.Check,
    CommonOptionBag.Verbose,
    CommonOptionBag.FormatPrint,
    DeveloperOptionBag.UseBaseFileName
  }.Concat(ParserOptions);

  public static IReadOnlyList<Option> VerificationOptions = new Option[] {
    CommonOptionBag.RelaxDefiniteAssignment,
    BoogieOptionBag.VerificationTimeLimit,
    CommonOptionBag.VerifyIncludedFiles,
    CommonOptionBag.ManualLemmaInduction,
    CommonOptionBag.SolverPath,
    CommonOptionBag.DisableNonLinearArithmetic,
    CommonOptionBag.IsolateAssertions,
    BoogieOptionBag.BoogieArguments,
    CommonOptionBag.VerificationLogFormat,
    CommonOptionBag.SolverResourceLimit,
    CommonOptionBag.SolverPlugin,
    CommonOptionBag.SolverLog,
  }.ToList();

  public static IReadOnlyList<Option> TranslationOptions = new Option[] {
    BoogieOptionBag.NoVerify,
    CommonOptionBag.EnforceDeterminism,
    CommonOptionBag.OptimizeErasableDatatypeWrapper,
    CommonOptionBag.TestAssumptions,
    DeveloperOptionBag.Bootstrapping
  }.Concat(VerificationOptions).ToList();

  public static IReadOnlyList<Option> ExecutionOptions = new Option[] {
    CommonOptionBag.Target,
    DeveloperOptionBag.SpillTranslation
  }.Concat(TranslationOptions).ToList();

  public static IReadOnlyList<Option> ConsoleOutputOptions = new List<Option>(new Option[] {
    DafnyConsolePrinter.ShowSnippets,
    DeveloperOptionBag.UseBaseFileName,
    DeveloperOptionBag.Print,
    DeveloperOptionBag.ResolvedPrint,
    DeveloperOptionBag.BoogiePrint,
    Printer.PrintMode,
    CommonOptionBag.WarningAsErrors,
  });

  public static IReadOnlyList<Option> ParserOptions = new List<Option>(new Option[] {
    CommonOptionBag.StdIn,
    BoogieOptionBag.Cores,
    CommonOptionBag.Libraries,
    CommonOptionBag.Plugin,
    CommonOptionBag.Prelude,
    Function.FunctionSyntaxOption,
    CommonOptionBag.QuantifierSyntax,
    CommonOptionBag.UnicodeCharacters,
    CommonOptionBag.ErrorLimit,
  });

  public static IReadOnlyList<Option> ResolverOptions = new List<Option>(new Option[] {
    CommonOptionBag.WarnShadowing,
    CommonOptionBag.WarnMissingConstructorParenthesis,
    PrintStmt.TrackPrintEffectsOption,
    CommonOptionBag.AllowAxioms,
  }).Concat(ParserOptions).ToList();

  IEnumerable<Option> Options { get; }

  Command Create();

  void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context);
}
