using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public interface ICommandSpec {
  string Name { get; }

  string Description { get; }

  IEnumerable<IOptionSpec> Options { get; }

  void PostProcess(DafnyOptions dafnyOptions, Options options);
}

class BuildCommand : ICommandSpec {
  public string Name => "build";
  public string Description => "Generate source files in the target language.";
  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.EmitExecutable = false;
    var noVerify = NoVerifyOption.Instance.Get(options);
    dafnyOptions.SpillTargetCode = noVerify ? 3U : 2U;
  }

  public IEnumerable<IOptionSpec> Options =>
    new IOptionSpec[] {
      OutputOption.Instance,
      TargetOption.Instance,
      NoVerifyOption.Instance,
      // CompileVerboseOption.Instance,
      UseRuntimeLibOption.Instance,
    }.Concat(CommandRegistry.CommonOptions);
}

class RunCommand : ICommandSpec {
  public string Name => "run";
  public string Description => "Run the program.";

  public IEnumerable<IOptionSpec> Options =>
    new IOptionSpec[] {
      TargetOption.Instance,
      NoVerifyOption.Instance,
    }.Concat(CommandRegistry.CommonOptions);

  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.EmitExecutable = true;
    dafnyOptions.RunAfterCompile = true;
    dafnyOptions.ForceCompile = NoVerifyOption.Instance.Get(options);
    dafnyOptions.CompileVerbose = false;
  }
}

class VerifyCommand : ICommandSpec {
  public string Name => "verify";
  public string Description => "Verify the program.";
  public IEnumerable<IOptionSpec> Options => CommandRegistry.CommonOptions;

  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.EmitExecutable = false;
  }
}
