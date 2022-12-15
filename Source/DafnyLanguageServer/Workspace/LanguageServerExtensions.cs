using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Server;
using System;
using Microsoft.Extensions.Options;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Extension methods to register the dafny workspace services to the language server implementation.
  /// </summary>
  public static class LanguageServerExtensions {
    /// <summary>
    /// Registers all services necessary to manage the dafny workspace.
    /// </summary>
    /// <param name="options">The language server where the workspace services should be registered to.</param>
    /// <param name="configuration">The configuration object holding the server configuration.</param>
    /// <returns>The language server enriched with the dafny workspace services.</returns>
    public static LanguageServerOptions WithDafnyWorkspace(this LanguageServerOptions options) {
      return options.WithServices(services => services.WithDafnyWorkspace());
    }

    private static IServiceCollection WithDafnyWorkspace(this IServiceCollection services) {
      return services
        .AddSingleton<IDocumentDatabase>(serviceProvider => new DocumentManagerDatabase(serviceProvider))
        .AddSingleton<IDafnyParser>(serviceProvider => DafnyLangParser.Create(serviceProvider.GetRequiredService<ILogger<DafnyLangParser>>()))
        .AddSingleton<ITextDocumentLoader>(CreateTextDocumentLoader)
        .AddSingleton<INotificationPublisher, NotificationPublisher>()
        .AddSingleton<ITextChangeProcessor, TextChangeProcessor>()
        .AddSingleton<IRelocator, Relocator>()
        .AddSingleton<ISymbolGuesser, SymbolGuesser>()
        .AddSingleton<ICompilationStatusNotificationPublisher, CompilationStatusNotificationPublisher>()
        .AddSingleton<ITelemetryPublisher, TelemetryPublisher>();
    }

    public static TextDocumentLoader CreateTextDocumentLoader(IServiceProvider services) {
      return TextDocumentLoader.Create(
        services.GetRequiredService<IDafnyParser>(),
        services.GetRequiredService<ISymbolResolver>(),
        services.GetRequiredService<ISymbolTableFactory>(),
        services.GetRequiredService<IGhostStateDiagnosticCollector>(),
        services.GetRequiredService<ICompilationStatusNotificationPublisher>(),
        services.GetRequiredService<ILoggerFactory>(),
        services.GetRequiredService<INotificationPublisher>()
      );
    }
  }
}
