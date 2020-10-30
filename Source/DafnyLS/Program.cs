using Microsoft.Dafny.LanguageServer.Handlers;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using NLog;
using NLog.Web;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using OmniSharp.Extensions.LanguageServer.Server;
using System;
using System.Reflection;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer {
  public class Program {
    private static string DafnyVersion {
      get {
        var version = Assembly.GetExecutingAssembly().GetName().Version!;
        return $"{version.Major}.{version.Minor}.{version.Build}";
      }
    }

    private static async Task Main() {
      try {
        var server = await OmniSharp.Extensions.LanguageServer.Server.LanguageServer.From(
          options => options
            .WithInput(Console.OpenStandardInput())
            .WithOutput(Console.OpenStandardOutput())
            .ConfigureLogging(SetupLogging)
            .WithDafnyLanguage()
            .WithDafnyWorkspace()
            .WithDafnyHandlers()
            .OnInitialize(Initialize)
            .OnStarted(Started)
        );
        await server.WaitForExit;
      } finally {
        LogManager.Shutdown();
      }
    }

    private static Task Initialize(ILanguageServer server, InitializeParams request, CancellationToken cancellationToken) {
      var logger = server.GetRequiredService<ILogger<Program>>();
      logger.LogTrace("initializing service");
      return Task.CompletedTask;
    }

    private static void SetupLogging(ILoggingBuilder logging) {
      logging.ClearProviders()
        .AddNLog("nlog.config")
        // The log-level is managed by NLog.
        .SetMinimumLevel(Microsoft.Extensions.Logging.LogLevel.Trace);
    }

    private static Task Started(ILanguageServer server, InitializeResult result, CancellationToken cancellationToken) {
      // TODO this currently only sent to get rid of the "Server answer pending" of the VSCode plugin.
      server.SendNotification("serverStarted", DafnyVersion);
      server.SendNotification("dafnyLanguageServerVersionReceived", DafnyVersion);
      return Task.CompletedTask;
    }
  }
}
