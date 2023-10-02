using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class TranslateCommand : ICommandSpec {
  public IEnumerable<Option> Options =>
    new Option[] {
      CommonOptionBag.Output,
      CommonOptionBag.IncludeRuntimeOption,
    }.Concat(ICommandSpec.TranslationOptions).
      Concat(ICommandSpec.ConsoleOutputOptions).
      Concat(ICommandSpec.ResolverOptions);

  public Command Create() {
    var result = new Command("translate", "Translate Dafny sources to source and build files in a specified language.");
    
    result.AddCommand(new Command("cs", "C#"));
    result.AddCommand(new Command("go", "GoLang"));
    result.AddCommand(new Command("js", "JavaScript"));
    result.AddCommand(new Command("java"));
    result.AddCommand(new Command("py", "Python"));
    result.AddCommand(new Command("cpp", "C++. This back-end has various limitations (see Docs/Compilation/Cpp.md). This includes lack of support for BigIntegers (aka int), most higher order functions, and advanced features like traits or co-inductive types."));
    foreach (var subCommand in result.Subcommands) {
      subCommand.AddArgument(ICommandSpec.FilesArgument);
    }
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
    var noVerify = dafnyOptions.Get(BoogieOptionBag.NoVerify);
    dafnyOptions.CompilerName = context.ParseResult.CommandResult.Command.Name;
    dafnyOptions.SpillTargetCode = noVerify ? 3U : 2U;
  }
}
