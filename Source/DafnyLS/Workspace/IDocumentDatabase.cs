using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Diagnostics.CodeAnalysis;
using System.Threading;

namespace DafnyLS.Workspace {
  /// <summary>
  /// Stores and manages the provided documents.
  /// </summary>
  internal interface IDocumentDatabase {
    /// <summary>
    /// Closes the document with the specified ID.
    /// </summary>
    /// <param name="documentId">The ID of the document to close.</param>
    /// <returns><c>true</c> if the document was closed successfully, <c>false</c> if no such document was opened.</returns>
    bool CloseDocument(TextDocumentIdentifier documentId);

    /// <summary>
    /// Loads (or updates if newer) the specified document into the database.
    /// </summary>
    /// <param name="document">The document to load.</param>
    /// <returns><c>true</c> if the document was loaded successfully, <c>false</c> if a newer version of the specified document was already present.</returns>
    bool LoadDocument(TextDocumentItem document);

    /// <summary>
    /// Updates a document with the specified changes.
    /// </summary>
    /// <param name="documentChange">The change request containing the actual changes.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns><c>true</c> if the updates were successfully merged, <c>false</c> if a newer document version was present.</returns>
    bool UpdateDocument(DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken);

    /// <summary>
    /// Tries to resolve a document with the specified identifier.
    /// </summary>
    /// <param name="documentId">The identifier of the document to resolve.</param>
    /// <param name="document">An instance of the managed document, <c>null</c> if the specified document was not found.</param>
    /// <returns><c>true</c> if the document was resolved successfully, <c>false</c> otherwise.</returns>
    bool TryGetDocument(TextDocumentIdentifier documentId, [NotNullWhen(true)] out TextDocumentItem? document);
  }
}
