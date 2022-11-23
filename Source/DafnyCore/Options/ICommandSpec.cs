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

  public static IReadOnlyList<IOptionSpec> ExecutionOptions = new IOptionSpec[] {
    NoVerifyOption.Instance,
    EnforceDeterminismOption.Instance,
  }.ToList();

  public static IReadOnlyList<IOptionSpec> CommonOptions = new List<IOptionSpec>(new IOptionSpec[] {
    CoresOption.Instance,
    LibraryOption.Instance,
    ShowSnippetsOption.Instance,
    PluginOption.Instance,
    BoogieOption.Instance,
    PreludeOption.Instance,
    UseBaseFileNameOption.Instance,
    PrintOption.Instance,
    ResolvedPrintOption.Instance,
    BoogiePrintOption.Instance,
    RelaxDefiniteAssignment.Instance,
    FunctionSyntaxOption.Instance,
    QuantifierSyntaxOption.Instance,
    WarnShadowingOption.Instance,
    WarnMissingConstructorParenthesisOption.Instance,
    WarningAsErrorsOption.Instance,
    TrackPrintEffects.Instance,
    DisableNonLinearArithmeticOption.Instance
  });

  IEnumerable<IOptionSpec> Options { get; }

  Command Create();

  void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context);
}
