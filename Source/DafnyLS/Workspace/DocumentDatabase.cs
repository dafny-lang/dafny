using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Concurrent;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Threading;

namespace DafnyLS.Workspace {
  /// <summary>
  /// Thread-safe and obstruction free document database implementation.
  /// </summary>
  /// <remarks>
  /// The current implementation only supports full document updates (not deltas).
  /// </remarks>
  internal class DocumentDatabase : IDocumentDatabase {
    private readonly ILogger _logger;
    private readonly ConcurrentDictionary<DocumentUri, TextDocumentItem> _documents = new ConcurrentDictionary<DocumentUri, TextDocumentItem>();

    public DocumentDatabase(ILogger<DocumentDatabase> logger) {
      _logger = logger;
    }

    public bool LoadDocument(TextDocumentItem document) {
      if(_documents.AddOrUpdate(document.Uri, document, (uri, old) => document.Version > old.Version ? document : old) != document) {
        _logger.LogDebug("a newer version of {} was already loaded", document.Uri);
        return false;
      }
      return true;
    }

    public bool CloseDocument(TextDocumentIdentifier documentId) {
      if(!_documents.TryRemove(documentId.Uri, out var _)) {
        _logger.LogTrace("the document {} was already closed", documentId);
        return false;
      }
      return true;
    }
    
    public bool UpdateDocument(DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      var documentId = documentChange.TextDocument;
      while (_documents.TryGetValue(documentId.Uri, out var oldDocument)) {
        cancellationToken.ThrowIfCancellationRequested();
        if (documentId.Version < oldDocument.Version) {
          _logger.LogDebug("skipping update of {} since the current version is newer (old={} < new={})",
            documentId.Uri, oldDocument.Version, documentId.Version);
          return false;
        }
        if(_documents.TryUpdate(documentId.Uri, MergeDocumentChanges(oldDocument, documentChange), oldDocument)) {
          return true;
        }
      }
      _logger.LogWarning("received update for untracked document {}", documentId.Uri);
      return false;
    }

    private TextDocumentItem MergeDocumentChanges(TextDocumentItem oldDocument, DidChangeTextDocumentParams documentChange) {
      return new TextDocumentItem {
        LanguageId = oldDocument.LanguageId,
        Uri = oldDocument.Uri,
        Version = documentChange.TextDocument.Version,
        // TODO The full document is synchronized at this time. So there should be exactly one change.
        Text = documentChange.ContentChanges.Single().Text
      };
    }

    public bool TryGetDocument(TextDocumentIdentifier documentId, [NotNullWhen(true)] out TextDocumentItem? document) {
      return _documents.TryGetValue(documentId.Uri, out document);
    }
  }
}
