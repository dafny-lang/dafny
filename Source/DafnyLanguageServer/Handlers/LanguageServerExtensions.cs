using Microsoft.Dafny.LanguageServer.Handlers.Custom;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Server;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  /// <summary>
  /// Extension methods to register the dafny related handlers to interact with the language server.
  /// </summary>
  public static class LanguageServerExtensions {
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
        .WithHandler<DafnyDefinitionHandler>()
        .WithHandler<DafnyCompletionHandler>()
        .WithHandler<DafnySignatureHelpHandler>()
        .WithHandler<DafnyCounterExampleHandler>()
        .WithHandler<DafnyCodeActionHandler>()
        .WithHandler<VerificationHandler>();
    }
  }
}
