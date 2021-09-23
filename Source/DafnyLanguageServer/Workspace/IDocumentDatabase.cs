using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Diagnostics.CodeAnalysis;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Stores and manages the provided documents.
  /// </summary>
  public interface IDocumentDatabase {
    /// <summary>
    /// Closes the document with the specified ID.
    /// </summary>
    /// <param name="documentId">The ID of the document to close.</param>
    /// <returns>The closed dafny document, <c>null</c> if no such document was opened.</returns>
    DafnyDocument? CloseDocument(TextDocumentIdentifier documentId);

    /// <summary>
    /// Loads (or updates if newer) the specified document into the database.
    /// </summary>
    /// <param name="document">The document to load.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>
    /// A dafny document representing the loaded text document.
    /// If there was a newer existing text document already loaded, it will be returned instead.
    /// </returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    Task<DafnyDocument> LoadDocumentAsync(TextDocumentItem document, CancellationToken cancellationToken);

    /// <summary>
    /// Updates a document with the specified changes.
    /// </summary>
    /// <param name="documentChange">The change request containing the actual changes.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>
    /// The newly generated dafny document if the merge was applied (i.e., the change was newer).
    /// If there was a newer existing text document already loaded, it will be returned instead.
    /// In the case that the update was sent for an unloaded document, <c>null</c> will be returned.
    /// </returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    Task<DafnyDocument?> UpdateDocumentAsync(DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken);

    /// <summary>
    /// Notifies the document database that the given document was saved.
    /// </summary>
    /// <param name="documentId">The ID of the document that was saved.</param>
    /// <param name="cancellationToken">A token to cancel the save operation before its completion.</param>
    /// <returns>The saved document.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    Task<DafnyDocument?> SaveDocumentAsync(TextDocumentIdentifier documentId, CancellationToken cancellationToken);

    /// <summary>
    /// Tries to resolve a document with the specified identifier.
    /// </summary>
    /// <param name="documentId">The ID of the document to resolve.</param>
    /// <param name="document">An instance of the managed document, <c>null</c> if the specified document was not found.</param>
    /// <returns><c>true</c> if the document was resolved successfully, <c>false</c> otherwise.</returns>
    bool TryGetDocument(TextDocumentIdentifier documentId, [NotNullWhen(true)] out DafnyDocument? document);
  }
}
