using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Handlers.Custom;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions {
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
      client.OpenDocument(documentItem);
      return client.WaitForNotificationCompletionAsync(documentItem.Uri, cancellationToken);
    }

    public static Task<bool> RunSymbolVerification(this ILanguageClient client, TextDocumentIdentifier textDocumentIdentifier, Position position, CancellationToken cancellationToken) {
      return client.SendRequest(
        new VerificationParams() { TextDocument = textDocumentIdentifier, Position = position },
        cancellationToken);
    }

    public static Task CancelSymbolVerification(this ILanguageClient client, TextDocumentIdentifier textDocumentIdentifier,
      Position position, CancellationToken cancellationToken) {
      return client.SendRequest(
        new CancelVerificationParams() { TextDocument = textDocumentIdentifier, Position = position },
        cancellationToken);
    }

    public static void SaveDocument(this ILanguageClient client, TextDocumentItem documentItem) {
      client.DidSaveTextDocument(new DidSaveTextDocumentParams {
        TextDocument = documentItem
      });
    }

    public static Task SaveDocumentAndWaitAsync(this ILanguageClient client, TextDocumentItem documentItem, CancellationToken cancellationToken) {
      client.SaveDocument(documentItem);
      return client.WaitForNotificationCompletionAsync(documentItem.Uri, cancellationToken);
    }

    public static Task ChangeDocumentAndWaitAsync(this ILanguageClient client, DidChangeTextDocumentParams change, CancellationToken cancellationToken) {
      client.DidChangeTextDocument(change);
      return client.WaitForNotificationCompletionAsync(change.TextDocument.Uri, cancellationToken);
    }

    public static Task WaitForNotificationCompletionAsync(this ILanguageClient client, DocumentUri documentUri, CancellationToken cancellationToken) {
      // The underlying implementation of OpenDocument is non-blocking (DidOpenTextDocument).
      // Since we query the document database directly, we use a placeholder request to ensure
      // that the DidOpenTextDocument has been fully processed.
      return client.RequestHover(new HoverParams { Position = (0, 0), TextDocument = documentUri }, cancellationToken);
    }
  }
}
