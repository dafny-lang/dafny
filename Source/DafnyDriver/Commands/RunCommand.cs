using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.CommandLine.Parsing;
using System.Data;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using DafnyCore;

namespace Microsoft.Dafny;

public static class RunCommand {
  private static readonly Argument<IEnumerable<string>> UserProgramArguments;

  public static readonly Option<IEnumerable<string>> Inputs = new("--input", "Specify an additional input file.") {
    ArgumentHelpName = "file"
  };

  static RunCommand() {
    UserProgramArguments = new Argument<IEnumerable<string>>("program-arguments", "arguments to the Dafny program");
    UserProgramArguments.SetDefaultValue(new List<string>());

    DafnyOptions.RegisterLegacyBinding(Inputs, (options, files) => {
      foreach (var file in files) {
        options.CliRootSourceUris.Add(new Uri(Path.GetFullPath(file)));
      }
    });

    DafnyOptions.RegisterLegacyBinding(MainOverride, (options, value) => {
      options.MainMethod = value;
    });

    OptionRegistry.RegisterOption(Inputs, OptionScope.Cli);
    OptionRegistry.RegisterOption(MainOverride, OptionScope.Cli);
    OptionRegistry.RegisterOption(CommonOptionBag.BuildFile, OptionScope.Cli);
  }

  public static readonly Option<string> MainOverride =
    new("--main-method", "Override the method called to start the program, using a fully qualified method name.");

  public static IEnumerable<Option> Options =>
    new Option[] {
      Inputs,
      MainOverride,
      CommonOptionBag.BuildFile,
    }.Concat(DafnyCommands.ExecutionOptions).
      Concat(DafnyCommands.ConsoleOutputOptions).
      Concat(DafnyCommands.ResolverOptions);

  public static Command Create() {
    var result = new Command("run", "Run the program.");
    result.AddArgument(DafnyCommands.FileArgument);
    result.AddArgument(UserProgramArguments);
    // result.TreatUnmatchedTokensAsErrors = false;
    foreach (var option in Options) {
      result.AddOption(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, context) => {
      await CheckForMistypedDafnyOption(context, options);
      options.MainArgs = context.ParseResult.GetValueForArgument(UserProgramArguments).ToList();
      options.Compile = true;
      options.RunAfterCompile = true;
      options.ForceCompile = options.Get(BoogieOptionBag.NoVerify);

      return await SynchronousCliCompilation.Run(options);
    });
    return result;
  }

  /// <summary>
  /// This check tries to determine if users tried to use a Dafny option but mistyped the option name.
  /// This check uses the position of a `--` token in a way that is not compliant with POSIX conventions,
  /// but we believe this is worth the improved feedback.
  /// </summary>
  private static async Task CheckForMistypedDafnyOption(InvocationContext context, DafnyOptions options) {
    var userProgramArgumentTokens = context.ParseResult.FindResultFor(UserProgramArguments)!.Tokens.Select(t => t.Value).ToHashSet();
    foreach (var token in context.ParseResult.Tokens) {
      // This check may lead to false positives if CLI is given the same value twice,
      // once as a Dafny option and once as a user program argument
      // The problem is that the tokens in context.ParseResult.FindResultFor(UserProgramArguments)!.Tokens
      // are not aware of their position in the argument list,
      // and cannot be compared with the tokens in context.ParseResult.Tokens,
      // so it's not possible to determine whether they occurred before the -- or not.
      var valueOfUserProgramArgument = userProgramArgumentTokens.Contains(token.Value);
      if (token.Value.StartsWith("--") && token.Type == TokenType.Argument && valueOfUserProgramArgument) {
        await options.OutputWriter.Status($"Argument {token.Value} is not a Dafny option so it was interpreted as an argument to the user program, even though it starts with '--'. Move this argument to after a `--` token to silence this message.");
      }
      if (token.Value == "--") {
        break;
      }
    }
  }
}
