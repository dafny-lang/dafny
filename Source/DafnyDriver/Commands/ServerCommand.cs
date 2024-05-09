using System.Collections.Generic;
using System.CommandLine;
using DafnyCore;
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

    DooFile.RegisterNoChecksNeeded(ProjectManager.Verification, false);
    DooFile.RegisterNoChecksNeeded(GhostStateDiagnosticCollector.GhostIndicators, false);
    DooFile.RegisterNoChecksNeeded(GutterIconAndHoverVerificationDetailsManager.LineVerificationStatus, false);
    DooFile.RegisterNoChecksNeeded(LanguageServer.VerifySnapshots, false);
    DooFile.RegisterNoChecksNeeded(DafnyLangSymbolResolver.UseCaching, false);
    DooFile.RegisterNoChecksNeeded(ProjectManager.UpdateThrottling, false);
    DooFile.RegisterNoChecksNeeded(ProjectManager.ReuseSolvers, false);
    DooFile.RegisterNoChecksNeeded(LegacySignatureAndCompletionTable.MigrateSignatureAndCompletionTable, false);
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
