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
  public interface IProjectDatabase : IDisposable {
    /// <summary>
    /// Closes the document with the specified ID.
    /// </summary>
    /// <param name="documentId">The ID of the document to close.</param>
    /// <remarks>
    /// The task represents any outstanding work of the document. It should be awaited to ensure
    /// that no processing occurs after the document is closed.
    /// </remarks>
    Task CloseDocumentAsync(TextDocumentIdentifier documentId);

    /// <summary>
    /// Loads (or updates if newer) the specified document into the database.
    /// </summary>
    /// <param name="document">The document to load.</param>
    Task OpenDocument(TextDocumentItem document);

    /// <summary>
    /// Updates a document with the specified changes.
    /// </summary>
    /// <param name="documentChange">The change request containing the actual changes.</param>
    /// <returns>
    /// <exception cref="ArgumentException">Thrown if the specified document does not exist.</exception>
    Task UpdateDocument(DidChangeTextDocumentParams documentChange);

    /// <summary>
    /// Notifies the document database that the given document was saved.
    /// </summary>
    /// <param name="documentId">The ID of the document that was saved.</param>
    /// <exception cref="ArgumentException">Thrown if the specified document does not exist.</exception>
    Task SaveDocument(TextDocumentIdentifier documentId);

    Task<IdeState?> GetParsedDocumentNormalizeUri(TextDocumentIdentifier documentId);

    /// <summary>
    /// Tries to resolve a document with the specified identifier.
    /// </summary>
    /// <param name="documentId">The ID of the document to resolve.</param>
    /// <returns>An instance of the managed document, <c>null</c> if the specified document was not found.</returns>
    Task<IdeState?> GetResolvedDocumentAsyncNormalizeUri(TextDocumentIdentifier documentId);
    internal Task<IdeState?> GetResolvedDocumentAsyncInternal(TextDocumentIdentifier documentId);

    /// <summary>
    /// Tries to resolve a verified document with the specified identifier.
    /// </summary>
    /// <param name="documentId">The ID of the document to resolve.</param>
    /// <returns>An instance of the managed document, <c>null</c> if the specified document was not found.</returns>
    Task<CompilationAfterParsing?> GetLastDocumentAsync(TextDocumentIdentifier documentId);

    Task<ProjectManager?> GetProjectManager(TextDocumentIdentifier documentId);

    IEnumerable<ProjectManager> Managers { get; }
    Task<DafnyProject> GetProject(Uri uri);
  }
}
