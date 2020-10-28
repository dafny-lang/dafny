using DafnyLS.Language;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Concurrent;
using System.Diagnostics.CodeAnalysis;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Workspace {
  /// <summary>
  /// Thread-safe document database implementation.
  /// </summary>
  /// <remarks>
  /// The current implementation only supports full document updates (not deltas).
  /// </remarks>
  public class DocumentDatabase : IDocumentDatabase {
    private readonly ILogger _logger;
    private readonly ConcurrentDictionary<DocumentUri, DafnyDocument> _documents = new ConcurrentDictionary<DocumentUri, DafnyDocument>();
    private readonly ITextDocumentLoader _documentLoader;
    private readonly IDocumentUpdater _documentUpdater;

    public DocumentDatabase(ILogger<DocumentDatabase> logger, ITextDocumentLoader documentLoader, IDocumentUpdater documentUpdater) {
      _logger = logger;
      _documentLoader = documentLoader;
      _documentUpdater = documentUpdater;
    }

    public async Task<DafnyDocument> LoadDocumentAsync(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      var dafnyDocument = await _documentLoader.LoadAsync(textDocument, cancellationToken);
      var databaseDocument = _documents.AddOrUpdate(textDocument.Uri, dafnyDocument, (uri, old) => dafnyDocument.Version > old.Version ? dafnyDocument : old);
      if (databaseDocument != dafnyDocument) {
        _logger.LogDebug("a newer version of {} was already loaded", textDocument.Uri);
      }
      return databaseDocument;
    }

    public bool CloseDocument(TextDocumentIdentifier documentId) {
      if(!_documents.TryRemove(documentId.Uri, out var _)) {
        _logger.LogTrace("the document {} was already closed", documentId);
        return false;
      }
      return true;
    }
    
    // TODO refresh loaded documents that depend on this document? Maybe at least when saving?
    public async Task<DafnyDocument?> UpdateDocumentAsync(DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      var documentId = documentChange.TextDocument;
      while (_documents.TryGetValue(documentId.Uri, out var oldDocument)) {
        cancellationToken.ThrowIfCancellationRequested();
        if (documentId.Version < oldDocument.Version) {
          _logger.LogDebug("skipping update of {} since the current version is newer (old={} < new={})",
            documentId.Uri, oldDocument.Version, documentId.Version);
          return oldDocument;
        }
        var mergedDocument = await _documentUpdater.ApplyChangesAsync(oldDocument, documentChange, cancellationToken);
        if (_documents.TryUpdate(documentId.Uri, mergedDocument, oldDocument)) {
          return mergedDocument;
        }
      }
      _logger.LogWarning("received update for untracked document {}", documentId.Uri);
      return null;
    }

    public bool TryGetDocument(TextDocumentIdentifier documentId, [NotNullWhen(true)] out DafnyDocument? document) {
      return _documents.TryGetValue(documentId.Uri, out document);
    }
  }
}
