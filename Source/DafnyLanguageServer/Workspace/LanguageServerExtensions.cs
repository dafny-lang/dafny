using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Server;

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
    public static LanguageServerOptions WithDafnyWorkspace(this LanguageServerOptions options, IConfiguration configuration) {
      return options.WithServices(services => services.WithDafnyWorkspace(configuration));
    }

    private static IServiceCollection WithDafnyWorkspace(this IServiceCollection services, IConfiguration configuration) {
      return services
        .Configure<DocumentOptions>(configuration.GetSection(DocumentOptions.Section))
        .AddSingleton<IDocumentDatabase, DocumentDatabase>()
        .AddSingleton<IDafnyParser>(serviceProvider => DafnyLangParser.Create(serviceProvider.GetRequiredService<ILogger<DafnyLangParser>>()))
        .AddSingleton<ITextDocumentLoader, TextDocumentLoader>()
        .AddSingleton<IDiagnosticPublisher, DiagnosticPublisher>()
        .AddSingleton<IDocumentUpdater, DocumentUpdater>()
        .AddSingleton<ISymbolGuesser, SymbolGuesser>()
        .AddSingleton<ICompilationStatusNotificationPublisher, CompilationStatusNotificationPublisher>();
    }
  }
}
