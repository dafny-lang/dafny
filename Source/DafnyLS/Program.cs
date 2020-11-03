using Microsoft.Extensions.Logging;
using NLog;
using NLog.Web;
using OmniSharp.Extensions.LanguageServer.Server;
using System;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer {
  public class Program {
    private static async Task Main() {
      try {
        var server = await OmniSharp.Extensions.LanguageServer.Server.LanguageServer.From(
          options => options
            .WithInput(Console.OpenStandardInput())
            .WithOutput(Console.OpenStandardOutput())
            .ConfigureLogging(SetupLogging)
            .WithDafnyLanguageServer()
        );
        await server.WaitForExit;
      } finally {
        LogManager.Shutdown();
      }
    }

    private static void SetupLogging(ILoggingBuilder logging) {
      logging.ClearProviders()
        .AddNLog("nlog.config")
        // The log-level is managed by NLog.
        .SetMinimumLevel(Extensions.Logging.LogLevel.Trace);
    }
  }
}
