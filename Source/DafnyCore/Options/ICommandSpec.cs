using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.CommandLine.Parsing;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny;

public interface ICommandSpec {

  public static Argument<FileInfo> FileArgument { get; }

  private static ValidateSymbolResult<ArgumentResult> ValidateFileArgument() {
    return r => {
      var value = r.Tokens[0].Value;
      if (value.StartsWith("--")) {
        r.ErrorMessage = $"{value} is not a valid argument";
      }
    };
  }

  static ICommandSpec() {
    FilesArgument = new Argument<IEnumerable<FileInfo>>("file", "input files");
    FilesArgument.AddValidator(ValidateFileArgument());
  }
  public static Argument<IEnumerable<FileInfo>> FilesArgument { get; }

  public static IReadOnlyList<Option> VerificationOptions = new Option[] {
    BoogieOptionBag.VerificationTimeLimit,
    CommonOptionBag.VerifyIncludedFiles,
    CommonOptionBag.ManualLemmaInduction,
    CommonOptionBag.SolverPath,
  }.ToList();

  public static IReadOnlyList<Option> ExecutionOptions = new Option[] {
    CommonOptionBag.Target,
    BoogieOptionBag.NoVerify,
    CommonOptionBag.EnforceDeterminism,
    CommonOptionBag.OptimizeErasableDatatypeWrapper,
  }.Concat(VerificationOptions).ToList();

  public static IReadOnlyList<Option> ConsoleOutputOptions = new List<Option>(new Option[] {
    DafnyConsolePrinter.ShowSnippets,
    DeveloperOptionBag.UseBaseFileName,
    DeveloperOptionBag.Print,
    DeveloperOptionBag.ResolvedPrint,
    DeveloperOptionBag.BoogiePrint,
    Printer.PrintMode,
    CommonOptionBag.WarningAsErrors,
  });

  public static IReadOnlyList<Option> CommonOptions = new List<Option>(new Option[] {
    BoogieOptionBag.Cores,
    CommonOptionBag.Libraries,
    CommonOptionBag.Plugin,
    BoogieOptionBag.BoogieArguments,
    CommonOptionBag.Prelude,
    CommonOptionBag.RelaxDefiniteAssignment,
    Function.FunctionSyntaxOption,
    CommonOptionBag.QuantifierSyntax,
    CommonOptionBag.WarnShadowing,
    CommonOptionBag.WarnMissingConstructorParenthesis,
    PrintStmt.TrackPrintEffectsOption,
    CommonOptionBag.DisableNonLinearArithmetic,
    CommonOptionBag.UnicodeCharacters,
  });

  IEnumerable<Option> Options { get; }

  Command Create();

  void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context);
}
