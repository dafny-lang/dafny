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

    DooFile.RegisterNoChecksNeeded(
      ProjectManager.Verification,
      GhostStateDiagnosticCollector.GhostIndicators,
      GutterIconAndHoverVerificationDetailsManager.LineVerificationStatus,
      LanguageServer.VerifySnapshots,
      DafnyLangSymbolResolver.UseCaching,
      ProjectManager.UpdateThrottling
    );
  }

  private static Command Create() {
    var result = new Command("server", "Start the Dafny language server");
    foreach (var option in LanguageServer.Options) {
      result.Add(option);
    }
    DafnyCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, context) => {
      LanguageServer.ConfigureDafnyOptionsForServer(options);
      await LanguageServer.Start(options);
      return 0;
    });
    return result;
  }

}
