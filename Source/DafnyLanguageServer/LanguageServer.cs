﻿using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Server;
using Serilog;
using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Reflection;
using System.Text;
using System.Threading.Tasks;
using DafnyCore;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.DependencyInjection;
using OmniSharpLanguageServer = OmniSharp.Extensions.LanguageServer.Server.LanguageServer;

namespace Microsoft.Dafny.LanguageServer {
  public class LanguageServer {

    public static IEnumerable<Option> Options => new Option[] {
        BoogieOptionBag.NoVerify,
        ProjectManager.Verification,
        GhostStateDiagnosticCollector.GhostIndicators,
        GutterIconAndHoverVerificationDetailsManager.LineVerificationStatus,
        VerifySnapshots,
        DafnyLangSymbolResolver.UseCaching,
        ProjectManager.UpdateThrottling,
        CachingProjectFileOpener.ProjectFileCacheExpiry,
        DeveloperOptionBag.SplitPrint,
        DeveloperOptionBag.PassivePrint,
        DeveloperOptionBag.BoogiePrint,
        InternalDocstringRewritersPluginConfiguration.UseJavadocLikeDocstringRewriterOption,
        LegacySignatureAndCompletionTable.MigrateSignatureAndCompletionTable
      }.Concat(DafnyCommands.VerificationOptions).
      Concat(DafnyCommands.ResolverOptions);

    public static readonly Option<uint> VerifySnapshots = new("--cache-verification", @"
(experimental)
0 - do not use any verification result caching (default)
1 - use the basic verification result caching
2 - use the more advanced verification result caching
3 - use the more advanced caching and report errors according
  to the new source locations for errors and their
  related locations
".TrimStart()) {
      ArgumentHelpName = "level"
    };

    public static void ConfigureDafnyOptionsForServer(DafnyOptions dafnyOptions) {
      dafnyOptions.Set(Snippets.ShowSnippets, true);
    }

    public static async Task Start(DafnyOptions dafnyOptions) {
      var configuration = CreateConfiguration();
      InitializeLogger(dafnyOptions, configuration);

      dafnyOptions = new DafnyOptions(dafnyOptions, true);
      try {
        Action? shutdownServer = null;
        var server = await OmniSharpLanguageServer.From(
          options => options.WithServices(s => s.AddSingleton(dafnyOptions))
            .WithInput(Console.OpenStandardInput())
            .WithOutput(Console.OpenStandardOutput())
            .ConfigureConfiguration(builder => builder.AddConfiguration(configuration))
            .ConfigureLogging(SetupLogging)
            .WithUnhandledExceptionHandler(LogException)
            // ReSharper disable once AccessToModifiedClosure
            .WithDafnyLanguageServer(dafnyOptions, () => shutdownServer!())
        );
        // Prevent any other parts of the language server to actually write to standard output.
        await using var logWriter = new LogWriter();
        Console.SetOut(logWriter);
        shutdownServer = () => server.ForcefulShutdown();
        await server.WaitForExit;
      }
      finally {
        await Log.CloseAndFlushAsync();
      }
    }

    private static IConfiguration CreateConfiguration() {
      return new ConfigurationBuilder()
        .AddJsonFile("DafnyLanguageServer.appsettings.json", optional: true)
        .Build();
    }

    private static void InitializeLogger(DafnyOptions options, IConfiguration configuration) {
      // The environment variable is used so a log file can be explicitly created in the application dir.
      var logLevel = options.Get(CommonOptionBag.LogLevelOption);
      var logLocation = options.Get(CommonOptionBag.LogLocation) ?? Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
      Environment.SetEnvironmentVariable("DAFNYLS_APP_DIR", logLocation);
      LoggerConfiguration config = new LoggerConfiguration()
        .ReadFrom.Configuration(configuration)
        .MinimumLevel.Override("Microsoft.Dafny", logLevel);
      if (logLocation != null) {
        var logFile = Path.Combine(logLocation,
          "DafnyLanguageServerLog" + DateTime.Now.ToString().Replace("/", "_").Replace("\\", "_") + ".txt");
        config = config.WriteTo.File(logFile);
      }
      Log.Logger = config.CreateLogger();
    }

    private static void LogException(Exception exception) {
      Log.Logger.Error(exception, "captured unhandled exception");
    }

    private static void SetupLogging(ILoggingBuilder builder) {
      builder
        .ClearProviders()
        .AddSerilog(Log.Logger);
    }

    private class LogWriter : TextWriter {
      public override void Write(char value) {
        Log.Logger.Verbose("Unexpected console output: {value}", value);
      }

      public override void Write(string? value) {
        Log.Logger.Verbose("Unexpected console output: {value}", value);
      }

      public override Encoding Encoding { get; } = Encoding.ASCII;
    }
  }
}
