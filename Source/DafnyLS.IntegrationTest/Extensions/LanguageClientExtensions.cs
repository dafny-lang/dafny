using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace DafnyLS.IntegrationTest.Extensions {
  /// <summary>
  /// Extension methods for simplified interaction with the language client.
  /// </summary>
  public static class LanguageClientExtensions {
    public static void OpenDocument(this ILanguageClient client, TextDocumentItem documentItem) {
      client.DidOpenTextDocument(new DidOpenTextDocumentParams {
        TextDocument = documentItem
      });
    }
  }
}
