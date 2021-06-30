using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Server;
using Serilog;
using System;
using System.Threading.Tasks;
using OmniSharpLanguageServer = OmniSharp.Extensions.LanguageServer.Server.LanguageServer;

namespace Microsoft.Dafny.LanguageServer {
  public class Program {
    private static async Task Main(string[] args) {
      var configuration = CreateConfiguration(args);
      Log.Logger = CreateLogger(configuration);
      try {
        var server = await OmniSharpLanguageServer.From(
          options => options
            .WithInput(Console.OpenStandardInput())
            .WithOutput(Console.OpenStandardOutput())
            .ConfigureConfiguration(builder => builder.AddConfiguration(configuration))
            .ConfigureLogging(SetupLogging)
            .WithUnhandledExceptionHandler(LogException)
            .WithDafnyLanguageServer(configuration)
        );
        await server.WaitForExit;
      } finally {
        Log.CloseAndFlush();
      }
    }

    private static IConfiguration CreateConfiguration(string[] args) {
      return new ConfigurationBuilder()
        .AddJsonFile("appsettings.json", optional: true)
        .AddCommandLine(args)
        .Build();
    }

    private static Serilog.ILogger CreateLogger(IConfiguration configuration) {
      return new LoggerConfiguration()
        .ReadFrom.Configuration(configuration)
        .CreateLogger();
    }

    private static void LogException(Exception exception) {
      Log.Logger.Error(exception, "captured unhandled exception");
    }

    private static void SetupLogging(ILoggingBuilder builder) {
      builder
        .ClearProviders()
        .AddSerilog(Log.Logger);
    }
  }
}
