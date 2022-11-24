using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny.LanguageServer;

public class ServerCommand : ICommandSpec {

  public IEnumerable<IOptionSpec> Options => new IOptionSpec[] {
    VerificationOption.Instance,
    GhostIndicatorsOption.Instance,
    LineVerificationStatusOption.Instance,
    VerifySnapshotsOption.Instance,
    VerificationTimeLimitOption.Instance,
    EnforceDeterminismOption.Instance,
  }.Concat(ICommandSpec.CommonOptions);

  public Command Create() {
    var command = new Command("server", "Start the Dafny language server");
    return command;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    ConfigureDafnyOptionsForServer(dafnyOptions);
  }

  public static void ConfigureDafnyOptionsForServer(DafnyOptions dafnyOptions)
  {
    dafnyOptions.RunServer = true;
    ShowSnippetsOption.Instance.Set(dafnyOptions, true);
    dafnyOptions.PrintIncludesMode = DafnyOptions.IncludesModes.None;
    dafnyOptions.ProverOptions.AddRange(new List<string>()
    {
      "O:model_compress=false", // Replaced by "O:model.compact=false" if z3's version is > 4.8.6
      "O:model.completion=true",
      "O:model_evaluator.completion=true"
    });
  }
}

public class VerificationOption : CommandLineOption<AutoVerification> {
  public static readonly VerificationOption Instance = new();

  public override object DefaultValue => AutoVerification.OnChange;

  public override string LongName => "verify-on";

  public override string ArgumentName => "event";

  public override string Description => @"
(experimental)
Determine when to automatically verify the program. Choose from: Never, OnChange or OnSave.";

  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    throw new System.NotImplementedException();
  }

  public override string PostProcess(DafnyOptions options) {
    return null!;
  }
}

public class LineVerificationStatusOption : BooleanOption {
  public static readonly LineVerificationStatusOption Instance = new();
  public override string LongName => "show-line-verification-status";

  public override string Description => @"
(experimental, API will change)
Send notifications about the verification status of each line in the program.
".TrimStart();

  public override object DefaultValue => false;

  public override string PostProcess(DafnyOptions options) {
    return null!;
  }
}

public class GhostIndicatorsOption : BooleanOption {
  public static readonly GhostIndicatorsOption Instance = new();
  public override string LongName => "show-ghostness";
  public override string Description => @"
(experimental, API will change)
Send notifications that indicate which lines are ghost.".TrimStart();
  public override string PostProcess(DafnyOptions options) {
    return null!;
  }
}

public class VerifySnapshotsOption : NaturalNumberOption {
  public static readonly VerifySnapshotsOption Instance = new();
  public override object DefaultValue => 0U;
  public override string LongName => "cache-verification";
  public override string ArgumentName => "level";

  public override string Description => @"
(experimental)
0 - do not use any verification result caching (default)
1 - use the basic verification result caching
2 - use the more advanced verification result caching
3 - use the more advanced caching and report errors according
    to the new source locations for errors and their
    related locations
".TrimStart();
  public override string PostProcess(DafnyOptions options) {
    options.VerifySnapshots = (int)Get(options);
    return null!;
  }
}
