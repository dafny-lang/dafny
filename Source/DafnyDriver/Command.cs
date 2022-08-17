using System.Collections.Generic;
using System.Collections.Immutable;
using System.CommandLine;
using System.Linq;

namespace Microsoft.Dafny;

public interface ICommandSpec {
  string Name { get; }

  string Description { get; }

  ISet<IOptionSpec> Options { get; }

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

  public ISet<IOptionSpec> Options => new HashSet<IOptionSpec>(
    CommandRegistry.CommonOptions.Concat(new IOptionSpec[] {
      NoVerifyOption.Instance,
      TargetOption.Instance,
    }));
}

class RunCommand : ICommandSpec {
  public string Name => "run";
  public string Description => "Run the program.";

  public ISet<IOptionSpec> Options => new HashSet<IOptionSpec>(
    CommandRegistry.CommonOptions.Concat(new IOptionSpec[] {
      NoVerifyOption.Instance,
      TargetOption.Instance,
    }));

  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.EmitExecutable = true;
    dafnyOptions.RunAfterCompile = true;
    dafnyOptions.ForceCompile = NoVerifyOption.Instance.Get(options);
  }
}

class VerifyCommand : ICommandSpec {
  public string Name => "verify";
  public string Description => "Verify the program.";
  public ISet<IOptionSpec> Options => CommandRegistry.CommonOptions;

  public void PostProcess(DafnyOptions dafnyOptions, Options options) {
    dafnyOptions.EmitExecutable = false;
  }
}
