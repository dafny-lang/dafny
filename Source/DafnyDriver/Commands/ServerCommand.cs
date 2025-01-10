using System.CommandLine;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny.LanguageServer;

public class ServerCommand {
  public static readonly Command Instance = Create();

  private ServerCommand() {
  }

  static ServerCommand() {
    DafnyOptions.RegisterLegacyBinding(LanguageServer.VerifySnapshots, (options, u) => options.VerifySnapshots = (int)u);

    OptionRegistry.RegisterOption(ProjectManager.Verification, OptionScope.Cli);
    OptionRegistry.RegisterOption(GhostStateDiagnosticCollector.GhostIndicators, OptionScope.Cli);
    OptionRegistry.RegisterOption(GutterIconAndHoverVerificationDetailsManager.LineVerificationStatus, OptionScope.Cli);
    OptionRegistry.RegisterOption(LanguageServer.VerifySnapshots, OptionScope.Cli);
    OptionRegistry.RegisterOption(DafnyLangSymbolResolver.UseCaching, OptionScope.Cli);
    OptionRegistry.RegisterOption(ProjectManager.UpdateThrottling, OptionScope.Cli);
    OptionRegistry.RegisterOption(ProjectManager.ReuseSolvers, OptionScope.Cli);
    OptionRegistry.RegisterOption(LegacySignatureAndCompletionTable.MigrateSignatureAndCompletionTable, OptionScope.Cli);
  }

  private static Command Create() {
    var result = new Command("server", "Start the Dafny language server");
    foreach (var option in LanguageServer.Options) {
      result.Add(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, context) => {
      options.Set(DafnyFile.DoNotVerifyDependencies, true);
      LanguageServer.ConfigureDafnyOptionsForServer(options);
      await LanguageServer.Start(options);
      return 0;
    });
    return result;
  }

}
