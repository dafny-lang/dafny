using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Server;
using System;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Extension methods to register the dafny language services to the language server implementation.
  /// </summary>
  public static class LanguageServerExtensions {
    /// <summary>
    /// Registers all services necessary to manage the dafny language.
    /// </summary>
    /// <param name="options">The language server where the workspace services should be registered to.</param>
    /// <param name="configuration">The language server configuration.</param>
    /// <returns>The language server enriched with the dafny workspace services.</returns>
    public static LanguageServerOptions WithDafnyLanguage(this LanguageServerOptions options, IConfiguration configuration) {
      return options.WithServices(services => services.WithDafnyLanguage(configuration));
    }

    private static IServiceCollection WithDafnyLanguage(this IServiceCollection services, IConfiguration configuration) {
      return services
        .Configure<VerifierOptions>(configuration.GetSection(VerifierOptions.Section))
        .Configure<GhostOptions>(configuration.GetSection(GhostOptions.Section))
        .AddSingleton<IDafnyParser>(serviceProvider => DafnyLangParser.Create(serviceProvider.GetRequiredService<ILogger<DafnyLangParser>>()))
        .AddSingleton<ISymbolResolver, DafnyLangSymbolResolver>()
        .AddSingleton<IProgramVerifier>(CreateVerifier)
        .AddSingleton<ISymbolTableFactory, SymbolTableFactory>()
        .AddSingleton<IGhostStateDiagnosticCollector, GhostStateDiagnosticCollector>();
    }

    private static IProgramVerifier CreateVerifier(IServiceProvider serviceProvider) {
      return DafnyProgramVerifier.Create(
        serviceProvider.GetRequiredService<ILogger<DafnyProgramVerifier>>(),
        serviceProvider.GetRequiredService<IOptions<VerifierOptions>>()
      );
    }
  }
}
