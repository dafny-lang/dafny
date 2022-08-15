using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public interface ICommand {
  string Name { get; }

  string Help { get; }

  ISet<ICommandLineOption> Options { get; }

  void PostProcess(DafnyOptions dafnyOptions, Options options);
}

class BuildCommand : ICommand {
  public string Name => "build";
  public string Help => "Generate source file in the target language";
  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.Compile = false;
    var noVerify = NoVerifyOption.Instance.Get(options);
    dafnyOptions.SpillTargetCode = noVerify ? 3U : 2U;
  }

  public ISet<ICommandLineOption> Options => new HashSet<ICommandLineOption>(
    CommandRegistry.CommonOptions.Concat(new ICommandLineOption[] {
      NoVerifyOption.Instance,
      TargetOption.Instance,
    }));
}

class RunCommand : ICommand {
  public string Name => "run";
  public string Help => "Run the program";

  public ISet<ICommandLineOption> Options => new HashSet<ICommandLineOption>(
    CommandRegistry.CommonOptions.Concat(new ICommandLineOption[] {
      NoVerifyOption.Instance,
      TargetOption.Instance,
    }));

  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = true;
    dafnyOptions.ForceCompile = NoVerifyOption.Instance.Get(options);
  }
}

class VerifyCommand : ICommand {
  public string Name => "verify";
  public string Help => "Verify the program";
  public ISet<ICommandLineOption> Options => CommandRegistry.CommonOptions;

  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.Compile = false;
  }
}