using System;
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
    FilesArgument = new("file", r => {
      return r.Tokens.Where(t => !string.IsNullOrEmpty(t.Value)).Select(t => new FileInfo(t.Value)).ToList();
    }, true, "Dafny input files and/or a Dafny project file");
  }

  public static Argument<List<FileInfo>> FilesArgument { get; }

  public static IEnumerable<Option> FormatOptions => new Option[] {
    CommonOptionBag.Check,
    CommonOptionBag.Verbose,
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
    BoogieOptionBag.SolverPlugin,
    BoogieOptionBag.SolverLog,
    CommonOptionBag.JsonDiagnostics,
    BoogieOptionBag.VerificationErrorLimit,
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
    BoogieOptionBag.Cores,
    CommonOptionBag.Libraries,
    CommonOptionBag.Plugin,
    CommonOptionBag.Prelude,
    Function.FunctionSyntaxOption,
    CommonOptionBag.QuantifierSyntax,
    CommonOptionBag.UnicodeCharacters,
    CommonOptionBag.UseBaseFileName,
    CommonOptionBag.TypeSystemRefresh,
    CommonOptionBag.TypeInferenceDebug,
    CommonOptionBag.NewTypeInferenceDebug,
  });

  public static IReadOnlyList<Option> ResolverOptions = new List<Option>(new Option[] {
    CommonOptionBag.WarnShadowing,
    CommonOptionBag.WarnMissingConstructorParenthesis,
    PrintStmt.TrackPrintEffectsOption,
  }).Concat(ParserOptions).ToList();

  IEnumerable<Option> Options { get; }

  Command Create();

  void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context);
}
