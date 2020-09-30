using DafnyLS.Handlers;
using DafnyLS.Workspace;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using NLog;
using NLog.Web;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using OmniSharp.Extensions.LanguageServer.Server;
using System;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS {
  internal class Program {
    private static async Task Main() {
      try {
        var server = await LanguageServer.From(
          options => options
            .WithInput(Console.OpenStandardInput())
            .WithOutput(Console.OpenStandardOutput())
            .ConfigureLogging(SetupLogging)
            .WithDafnyWorkspace()
            .WithDafnyHandlers()
            .OnInitialize(Initialize)
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
  }
}
