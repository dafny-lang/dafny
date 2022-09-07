using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Stores and manages the provided documents.
  /// </summary>
  public interface IDocumentDatabase {
    /// <summary>
    /// Closes the document with the specified ID.
    /// </summary>
    /// <param name="documentId">The ID of the document to close.</param>
    /// <returns><c>true</c> if the document was present in the database.</returns>
    /// <remarks>
    /// The task represents any outstanding work of the document. It should be awaited to ensure
    /// that no processing occurs after the document is closed.
    /// </remarks>
    Task<bool> CloseDocumentAsync(TextDocumentIdentifier documentId);

    /// <summary>
    /// Loads (or updates if newer) the specified document into the database.
    /// </summary>
    /// <param name="document">The document to load.</param>
    void OpenDocument(DocumentTextBuffer document);

    /// <summary>
    /// Updates a document with the specified changes.
    /// </summary>
    /// <param name="documentChange">The change request containing the actual changes.</param>
    /// <returns>
    /// <exception cref="ArgumentException">Thrown if the specified document does not exist.</exception>
    void UpdateDocument(DidChangeTextDocumentParams documentChange);

    /// <summary>
    /// Notifies the document database that the given document was saved.
    /// </summary>
    /// <param name="documentId">The ID of the document that was saved.</param>
    /// <exception cref="ArgumentException">Thrown if the specified document does not exist.</exception>
    void SaveDocument(TextDocumentIdentifier documentId);

    /// <summary>
    /// Tries to resolve a document with the specified identifier.
    /// </summary>
    /// <param name="documentId">The ID of the document to resolve.</param>
    /// <returns>An instance of the managed document, <c>null</c> if the specified document was not found.</returns>
    Task<IdeState?> GetResolvedDocumentAsync(TextDocumentIdentifier documentId);

    /// <summary>
    /// Tries to resolve a verified document with the specified identifier.
    /// </summary>
    /// <param name="documentId">The ID of the document to resolve.</param>
    /// <returns>An instance of the managed document, <c>null</c> if the specified document was not found.</returns>
    Task<DocumentAfterParsing?> GetLastDocumentAsync(TextDocumentIdentifier documentId);

    DocumentManager? GetDocumentManager(TextDocumentIdentifier documentId);

    IEnumerable<DocumentManager> Documents { get; }
  }
}
