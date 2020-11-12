using Microsoft.Extensions.Logging;
using NLog;
using NLog.Web;
using OmniSharp.Extensions.LanguageServer.Server;
using System;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer {
  public class Program {
    private static readonly NLog.ILogger logger = LogManager.GetCurrentClassLogger();

    private static async Task Main() {
      try {
        var server = await OmniSharp.Extensions.LanguageServer.Server.LanguageServer.From(
          options => options
            .WithInput(Console.OpenStandardInput())
            .WithOutput(Console.OpenStandardOutput())
            .ConfigureLogging(SetupLogging)
            .WithUnhandledExceptionHandler(LogException)
            .WithDafnyLanguageServer()
        );
        await server.WaitForExit;
      } finally {
        LogManager.Shutdown();
      }
    }

    private static void LogException(Exception e) {
      logger.Error(e, "captured unhandled exception");
    }

    private static void SetupLogging(ILoggingBuilder logging) {
      logging.ClearProviders()
        .AddNLog("nlog.config")
        // The log-level is managed by NLog.
        .SetMinimumLevel(Extensions.Logging.LogLevel.Trace);
    }
  }
}
