using DafnyLS.Language.Symbols;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Server;

namespace DafnyLS.Language {
  /// <summary>
  /// Extension methods to register the dafny language services to the language server implementation.
  /// </summary>
  internal static class LanguageServerExtensions {
    /// <summary>
    /// Registers all services necessary to manage the dafny language.
    /// </summary>
    /// <param name="options">The language server where the workspace services should be registered to.</param>
    /// <returns>The language server enriched with the dafny workspace services.</returns>
    public static LanguageServerOptions WithDafnyLanguage(this LanguageServerOptions options) {
      return options.WithServices(services => services.WithDafnyLanguage());
    }

    private static IServiceCollection WithDafnyLanguage(this IServiceCollection services) {
      return services
        .AddSingleton<IDafnyParser>(serviceProvider => DafnyLangParser.Create(serviceProvider.GetRequiredService<ILogger<DafnyLangParser>>()))
        .AddSingleton<ISymbolResolver, DafnyLangSymbolResolver>()
        .AddSingleton<IDiagnosticPublisher, DiagnosticPublisher>();
    }
  }
}
