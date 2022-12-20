using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class TranslateCommand : ICommandSpec {
  public IEnumerable<Option> Options =>
    new Option[] {
      CommonOptionBag.Output,
      CommonOptionBag.CompileVerbose,
      CommonOptionBag.IncludeRuntime,
    }.Concat(ICommandSpec.TranslationOptions).
      Concat(ICommandSpec.ConsoleOutputOptions).
      Concat(ICommandSpec.CommonOptions);

  private static readonly Argument<string> Target = new("target",@"
cs - Translate to C#.
go - Translate to Go.
js - Translate to JavaScript.
java - Translate to Java.
py - Translate to Python.
cpp - Translate to C++.

Note that the C++ backend has various limitations (see Docs/Compilation/Cpp.md). This includes lack of support for BigIntegers (aka int), most higher order functions, and advanced features like traits or co-inductive types.".TrimStart()
  ) {
    HelpName = "language"
  };

  public Command Create() {
    var result = new Command("translate", "Generate source and build files in a specified target language.");
    result.AddArgument(Target);
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
    var noVerify = dafnyOptions.Get(BoogieOptionBag.NoVerify);
    dafnyOptions.SpillTargetCode = noVerify ? 3U : 2U;
  }
}
