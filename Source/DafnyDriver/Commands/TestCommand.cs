using System.Collections.Generic;
using System.CommandLine;
using DafnyCore;

namespace Microsoft.Dafny;

static class TestCommand {
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

  static TestCommand() {
    DafnyOptions.RegisterLegacyBinding(MethodsToTest, (o, v) => { o.MethodsToTest = v; });

    DooFile.RegisterNoChecksNeeded(MethodsToTest);
  }


  public static Command Create() {
    var result = new Command("test", "(Experimental) Execute every method in the program that's annotated with the {:test} attribute.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }

    DafnyCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => {
      options.Compile = true;
      options.RunAfterCompile = true;
      options.RunAllTests = true;
      options.ForceCompile = options.Get(BoogieOptionBag.NoVerify);
      options.MainMethod = RunAllTestsMainMethod.SyntheticTestMainName;
      return CompilerDriver.RunCompiler(options);
    });
    return result;
  }
}
