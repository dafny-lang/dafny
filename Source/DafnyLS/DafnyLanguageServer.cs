using Microsoft.Dafny.LanguageServer.Handlers;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using OmniSharp.Extensions.LanguageServer.Server;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer {
  public static class DafnyLanguageServer {
    private static string DafnyVersion {
      get {
        var version = typeof(DafnyLanguageServer).Assembly.GetName().Version!;
        return $"{version.Major}.{version.Minor}.{version.Build}";
      }
    }

    public static LanguageServerOptions WithDafnyLanguageServer(this LanguageServerOptions options) {
      return options
        .WithDafnyLanguage()
        .WithDafnyWorkspace()
        .WithDafnyHandlers()
        .OnInitialize(Initialize)
        .OnStarted(Started);
    }

    private static Task Initialize(ILanguageServer server, InitializeParams request, CancellationToken cancellationToken) {
      var logger = server.GetRequiredService<ILogger<Program>>();
      logger.LogTrace("initializing service");
      return Task.CompletedTask;
    }

    private static Task Started(ILanguageServer server, InitializeResult result, CancellationToken cancellationToken) {
      // TODO this currently only sent to get rid of the "Server answer pending" of the VSCode plugin.
      server.SendNotification("serverStarted", DafnyVersion);
      server.SendNotification("dafnyLanguageServerVersionReceived", DafnyVersion);
      return Task.CompletedTask;
    }
  }
}
