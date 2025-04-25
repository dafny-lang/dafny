using System.Collections.Generic;
using System.CommandLine;
using DafnyCore;

namespace Microsoft.Dafny;

static class TestCommand {

  static TestCommand() {
    DafnyOptions.RegisterLegacyBinding(MethodsToTest, (o, v) => { o.MethodsToTest = v; });

    OptionRegistry.RegisterOption(MethodsToTest, OptionScope.Cli);
  }

  public static IEnumerable<Option> Options =>
    new Option[] {
      CommonOptionBag.Output,
      MethodsToTest,
    }.Concat(DafnyCommands.ExecutionOptions).
      Concat(DafnyCommands.ConsoleOutputOptions).
      Concat(DafnyCommands.ResolverOptions);

  private static readonly Option<string> MethodsToTest = new("--methods-to-test",
    "A regex (over fully qualified names) selecting which methods or functions to test") {
  };

  public static Command Create() {
    var result = new Command("test", "(Experimental) Execute every method in the program that's annotated with the {:test} attribute.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => {
      options.Compile = true;
      options.RunAfterCompile = true;
      options.Set(RunAllTestsMainMethod.IncludeTestRunner, true);
      options.ForceCompile = options.Get(BoogieOptionBag.NoVerify);
      options.MainMethod = RunAllTestsMainMethod.SyntheticTestMainName;
      return SynchronousCliCompilation.Run(options);
    });
    return result;
  }

  public static void EnsureStaticConstructorHasRun() { }
}
