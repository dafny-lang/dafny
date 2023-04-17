using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

public class TestCommand : ICommandSpec {
  public IEnumerable<Option> Options =>
    new Option[] {
      CommonOptionBag.Output,
      MethodsToTest,
    }.Concat(ICommandSpec.ExecutionOptions).
      Concat(ICommandSpec.ConsoleOutputOptions).
      Concat(ICommandSpec.ResolverOptions);

  public static readonly Option<string> MethodsToTest = new("--methods-to-test",
    "A regex (over fully qualified names) selecting which methods or functions to test") {
  };

  static TestCommand() {
    DafnyOptions.RegisterLegacyBinding(MethodsToTest, (o, v) => { o.MethodsToTest = v; });
  }


  public Command Create() {
    var result = new Command("test", "(Experimental) Execute every method in the program that's annotated with the {:test} attribute.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = true;
    dafnyOptions.RunAllTests = true;
    dafnyOptions.ForceCompile = dafnyOptions.Get(BoogieOptionBag.NoVerify);
    dafnyOptions.CompileVerbose = false;
    dafnyOptions.MainMethod = RunAllTestsMainMethod.SyntheticTestMainName;
  }
}
