using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Server;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Extension methods to register the dafny language services to the language server implementation.
  /// </summary>
  public static class LanguageServerExtensions {
    /// <summary>
    /// Registers all services necessary to manage the dafny language.
    /// </summary>
    /// <param name="options">The language server where the workspace services should be registered to.</param>
    /// <param name="configuration">The configuration object holding the server configuration.</param>
    /// <returns>The language server enriched with the dafny workspace services.</returns>
    public static LanguageServerOptions WithDafnyLanguage(this LanguageServerOptions options, IConfiguration configuration) {
      return options.WithServices(services => services.WithDafnyLanguage(configuration));
    }

    private static IServiceCollection WithDafnyLanguage(this IServiceCollection services, IConfiguration configuration) {
      return services
        .Configure<DiagnosticOptions>(configuration.GetSection(DiagnosticOptions.Section))
        .AddSingleton<IDafnyParser>(serviceProvider => DafnyLangParser.Create(serviceProvider.GetRequiredService<ILogger<DafnyLangParser>>()))
        .AddSingleton<ISymbolResolver, DafnyLangSymbolResolver>()
        .AddSingleton<IProgramVerifier>(serviceProvider => DafnyProgramVerifier.Create(serviceProvider.GetRequiredService<ILogger<DafnyProgramVerifier>>()))
        .AddSingleton<ISymbolTableFactory, SymbolTableFactory>()
        .AddSingleton<IDiagnosticPublisher, DiagnosticPublisher>();
    }
  }
}
