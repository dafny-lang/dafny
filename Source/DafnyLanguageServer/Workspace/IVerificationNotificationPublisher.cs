using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish the verification
  /// status of a <see cref="DafnyDocument"/> to the LSP client.
  /// </summary>
  public interface IVerificationNotificationPublisher {
    /// <summary>
    /// Called when the verification of a document started.
    /// </summary>
    /// <param name="textDocument">The document whose verification started.</param>
    void Started(TextDocumentItem textDocument);

    /// <summary>
    /// Called when the verification of a document started.
    /// </summary>
    /// <param name="textDocument">The document whose verification started.</param>
    /// <param name="verified"><c>True</c> if the given document was successfully verified.</param>
    void Completed(TextDocumentItem textDocument, bool verified);
  }
}
