using Microsoft.Extensions.Configuration;
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
        LanguageServer.VerifySnapshots,
        DafnyLangSymbolResolver.UseCaching,
        ProjectManager.UpdateThrottling,
        DeveloperOptionBag.BoogiePrint,
        CommonOptionBag.EnforceDeterminism,
        CommonOptionBag.UseJavadocLikeDocstringRewriterOption
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
      dafnyOptions.Set(DafnyConsolePrinter.ShowSnippets, true);

      dafnyOptions.PrintIncludesMode = DafnyOptions.IncludesModes.None;

      // TODO This may be subject to change. See Microsoft.Boogie.Counterexample
      //      A dash means write to the textwriter instead of a file.
      // https://github.com/boogie-org/boogie/blob/b03dd2e4d5170757006eef94cbb07739ba50dddb/Source/VCGeneration/Couterexample.cs#L217
      dafnyOptions.ModelViewFile = "-";

      dafnyOptions.ProverOptions.AddRange(new List<string>()
      {
        "O:model_compress=false", // Replaced by "O:model.compact=false" if z3's version is > 4.8.6
        "O:model.completion=true",
        "O:model_evaluator.completion=true"
      });
    }

    public static async Task Start(DafnyOptions dafnyOptions) {
      var configuration = CreateConfiguration();
      InitializeLogger(configuration);

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
            .WithDafnyLanguageServer(() => shutdownServer!())
        );
        // Prevent any other parts of the language server to actually write to standard output.
        await using var logWriter = new LogWriter();
        Console.SetOut(logWriter);
        shutdownServer = () => server.ForcefulShutdown();
        await server.WaitForExit;
      }
      finally {
        Log.CloseAndFlush();
      }
    }

    private static IConfiguration CreateConfiguration() {
      return new ConfigurationBuilder()
        .AddJsonFile("DafnyLanguageServer.appsettings.json", optional: true)
        .Build();
    }

    private static void InitializeLogger(IConfiguration configuration) {
      // The environment variable is used so a log file can be explicitly created in the application dir.
      Environment.SetEnvironmentVariable("DAFNYLS_APP_DIR", Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location));
      Log.Logger = new LoggerConfiguration()
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
