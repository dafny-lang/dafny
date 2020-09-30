using Microsoft.Extensions.DependencyInjection;
using OmniSharp.Extensions.LanguageServer.Server;

namespace DafnyLS.Workspace {
  /// <summary>
  /// Extension methods to register the dafny workspace services to the language server implementation.
  /// </summary>
  internal static class LanguageServerExtensions {
    /// <summary>
    /// Registers all services necessary to manage the dafny workspace.
    /// </summary>
    /// <param name="options">The language server where the workspace services should be registered to.</param>
    /// <returns>The language server enriched with the dafny workspace services.</returns>
    public static LanguageServerOptions WithDafnyWorkspace(this LanguageServerOptions options) {
      return options.WithServices(services => services.WithDafnyWorkspace());
    }

    private static IServiceCollection WithDafnyWorkspace(this IServiceCollection services) {
      return services
        .AddSingleton<IDocumentDatabase, DocumentDatabase>()
        .AddSingleton<ISymbolResolver, SymbolResolver>();
    }
  }
}
