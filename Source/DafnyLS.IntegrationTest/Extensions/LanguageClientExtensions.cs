using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

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

    public static Task OpenDocumentAndWaitAsync(this ILanguageClient client, TextDocumentItem documentItem, CancellationToken cancellationToken) {
      // The underlying implementation of OpenDocument is non-blocking (DidOpenTextDocument).
      // Since we query the document database directly, we use a placeholder request to ensure
      // that the DidOpenTextDocument has been fully processed.
      client.OpenDocument(documentItem);
      return client.RequestHover(new HoverParams { Position = (0, 0), TextDocument = documentItem.Uri }, cancellationToken);
    }
  }
}
