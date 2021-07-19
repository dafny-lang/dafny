using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish the compilation
  /// status of a <see cref="DafnyDocument"/> to the LSP client.
  /// </summary>
  public interface ICompilationStatusNotificationPublisher {
    /// <summary>
    /// Called when the document had parser errors (syntax errors).
    /// </summary>
    /// <param name="textDocument">The document which could not be parsed.</param>
    void ParsingFailed(TextDocumentItem textDocument);

    /// <summary>
    /// Called when the document had resolver errors.
    /// </summary>
    /// <param name="textDocument">The document which could not be parsed.</param>
    void ResolutionFailed(TextDocumentItem textDocument);

    /// <summary>
    /// Called when the verification of a document started.
    /// </summary>
    /// <param name="textDocument">The document whose verification started.</param>
    void VerificationStarted(TextDocumentItem textDocument);

    /// <summary>
    /// Called when the verification of a document was succesful.
    /// </summary>
    /// <param name="textDocument">The document whose verification completed succesfully.</param>
    void VerificationSucceeded(TextDocumentItem textDocument);

    /// <summary>
    /// Called when the verification of a document failed.
    /// </summary>
    /// <param name="textDocument">The document whose verification failed.</param>
    void VerificationFailed(TextDocumentItem textDocument);
  }
}
