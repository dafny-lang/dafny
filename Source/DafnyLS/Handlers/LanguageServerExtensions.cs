using OmniSharp.Extensions.LanguageServer.Server;

namespace DafnyLS.Handlers {
  /// <summary>
  /// Extension methods to register the dafny related handlers to interact with the language server.
  /// </summary>
  internal static class LanguageServerExtensions {
    /// <summary>
    /// Registers all handlers necessary to provide the language server integration of dafny.
    /// </summary>
    /// <param name="options">The language server where the handlers should be registered to.</param>
    /// <returns>The language server enriched with the dafny handlers.</returns>
    public static LanguageServerOptions WithDafnyHandlers(this LanguageServerOptions options) {
      return options
        .WithHandler<DafnyTextDocumentHandler>()
        .WithHandler<DafnyDocumentSymbolHandler>()
        .WithHandler<DafnyHoverHandler>()
        .WithHandler<DafnyDefinitionHandler>();
    }
  }
}
